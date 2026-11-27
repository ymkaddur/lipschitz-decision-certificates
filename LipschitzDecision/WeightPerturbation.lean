import Mathlib

/-!
# Telescoping bound for weight perturbations of a deep network

A network on a normed space `E` alternates bounded linear layers `W k` with an activation `σ` that is
1-Lipschitz and fixes `0` (ReLU, for example), without biases:
`x_0 = x`, `x_(k+1) = σ (W_k x_k)`.

* `norm_net_le`: `‖x_K‖ ≤ (∏_(j<K) ‖W_j‖) ‖x‖`;
* `net_sub_le`: replacing every `W_k` by `Ŵ_k` (for instance its quantized version) moves the output by
  at most `∑_k (∏_(k<j<K) ‖W_j‖) ‖W_k - Ŵ_k‖ (∏_(j<k) ‖Ŵ_j‖) ‖x‖`;
* `top1_of_weight_budget`: on logits in `ι → ℝ` with the sup norm, if that budget is below half the
  margin of the original network, the perturbed network keeps the top-1 class. This is a per-layer
  error budget for decision preservation.
-/

namespace LipschitzDecision

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The network `x_0 = x`, `x_(k+1) = σ (W k x_k)`. -/
def net (σ : E → E) (W : ℕ → E →L[ℝ] E) (x : E) : ℕ → E
  | 0 => x
  | k + 1 => σ (W k (net σ W x k))

omit [NormedSpace ℝ E] in
/-- Activations that are 1-Lipschitz and fix `0` do not increase norms. -/
theorem norm_act_le (σ : E → E) (hσ : ∀ a b, ‖σ a - σ b‖ ≤ ‖a - b‖) (hσ0 : σ 0 = 0) (y : E) :
    ‖σ y‖ ≤ ‖y‖ := by
  simpa [hσ0] using hσ y 0

/-- Size of the output: `‖x_K‖ ≤ (∏_(j<K) ‖W_j‖) ‖x‖`. -/
theorem norm_net_le (σ : E → E) (hσ : ∀ a b, ‖σ a - σ b‖ ≤ ‖a - b‖) (hσ0 : σ 0 = 0)
    (W : ℕ → E →L[ℝ] E) (x : E) (K : ℕ) : ‖net σ W x K‖ ≤ (∏ j ∈ range K, ‖W j‖) * ‖x‖ := by
  induction K with
  | zero => simp [net]
  | succ K ih =>
    calc ‖net σ W x (K + 1)‖ = ‖σ (W K (net σ W x K))‖ := rfl
      _ ≤ ‖W K (net σ W x K)‖ := norm_act_le σ hσ hσ0 _
      _ ≤ ‖W K‖ * ‖net σ W x K‖ := (W K).le_opNorm _
      _ ≤ ‖W K‖ * ((∏ j ∈ range K, ‖W j‖) * ‖x‖) := by gcongr
      _ = (∏ j ∈ range (K + 1), ‖W j‖) * ‖x‖ := by rw [prod_range_succ]; ring

/-- **Telescoping weight-perturbation bound.** -/
theorem net_sub_le (σ : E → E) (hσ : ∀ a b, ‖σ a - σ b‖ ≤ ‖a - b‖) (hσ0 : σ 0 = 0)
    (W V : ℕ → E →L[ℝ] E) (x : E) (K : ℕ) :
    ‖net σ W x K - net σ V x K‖ ≤
      ∑ k ∈ range K, (∏ j ∈ Ico (k + 1) K, ‖W j‖) * ‖W k - V k‖ *
        (∏ j ∈ range k, ‖V j‖) * ‖x‖ := by
  induction K with
  | zero => simp [net]
  | succ K ih =>
    set a := net σ W x K
    set b := net σ V x K
    have step : ‖net σ W x (K + 1) - net σ V x (K + 1)‖ ≤
        ‖W K‖ * ‖a - b‖ + ‖W K - V K‖ * ‖b‖ := by
      calc ‖net σ W x (K + 1) - net σ V x (K + 1)‖ = ‖σ (W K a) - σ (V K b)‖ := rfl
        _ ≤ ‖W K a - V K b‖ := hσ _ _
        _ = ‖W K (a - b) + (W K - V K) b‖ := by
          congr 1
          simp only [map_sub, sub_apply]
          abel
        _ ≤ ‖W K (a - b)‖ + ‖(W K - V K) b‖ := norm_add_le _ _
        _ ≤ ‖W K‖ * ‖a - b‖ + ‖W K - V K‖ * ‖b‖ :=
          add_le_add ((W K).le_opNorm _) ((W K - V K).le_opNorm _)
    have hb := norm_net_le σ hσ hσ0 V x K
    have hsum : ‖W K‖ * (∑ k ∈ range K, (∏ j ∈ Ico (k + 1) K, ‖W j‖) * ‖W k - V k‖ *
        (∏ j ∈ range k, ‖V j‖) * ‖x‖) =
        ∑ k ∈ range K, (∏ j ∈ Ico (k + 1) (K + 1), ‖W j‖) * ‖W k - V k‖ *
          (∏ j ∈ range k, ‖V j‖) * ‖x‖ := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [prod_Ico_succ_top (by have := mem_range.mp hk; omega)]
      ring
    rw [sum_range_succ, Ico_self, prod_empty, one_mul, ← hsum]
    calc ‖net σ W x (K + 1) - net σ V x (K + 1)‖
        ≤ ‖W K‖ * ‖a - b‖ + ‖W K - V K‖ * ‖b‖ := step
      _ ≤ ‖W K‖ * (∑ k ∈ range K, (∏ j ∈ Ico (k + 1) K, ‖W j‖) * ‖W k - V k‖ *
            (∏ j ∈ range k, ‖V j‖) * ‖x‖) +
          ‖W K - V K‖ * ((∏ j ∈ range K, ‖V j‖) * ‖x‖) := by gcongr
      _ = ‖W K‖ * (∑ k ∈ range K, (∏ j ∈ Ico (k + 1) K, ‖W j‖) * ‖W k - V k‖ *
            (∏ j ∈ range k, ‖V j‖) * ‖x‖) +
          ‖W K - V K‖ * (∏ j ∈ range K, ‖V j‖) * ‖x‖ := by ring

/-- **Per-layer error budget for decisions.** On logits in `ι → ℝ` with the sup norm, if the
telescoping budget of the weight perturbation is below half the margin of the original network at
`x`, the perturbed network keeps the top-1 class at `x`. -/
theorem top1_of_weight_budget {ι : Type*} [Fintype ι] (σ : (ι → ℝ) → ι → ℝ)
    (hσ : ∀ a b, ‖σ a - σ b‖ ≤ ‖a - b‖) (hσ0 : σ 0 = 0) (W V : ℕ → (ι → ℝ) →L[ℝ] (ι → ℝ))
    (x : ι → ℝ) (K : ℕ) (i : ι) (ε : ℝ)
    (hbudget : ∑ k ∈ range K, (∏ j ∈ Ico (k + 1) K, ‖W j‖) * ‖W k - V k‖ *
        (∏ j ∈ range k, ‖V j‖) * ‖x‖ ≤ ε)
    (hm : ∀ j, j ≠ i → net σ W x K j + 2 * ε < net σ W x K i) :
    ∀ j, j ≠ i → net σ V x K j < net σ V x K i := by
  have hclose := (net_sub_le σ hσ hσ0 W V x K).trans hbudget
  have hc : ∀ k, |net σ W x K k - net σ V x K k| ≤ ε := fun k => by
    have := norm_le_pi_norm (net σ W x K - net σ V x K) k
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  intro j hj
  have h1 := abs_le.mp (hc j)
  have h2 := abs_le.mp (hc i)
  have := hm j hj
  linarith [h1.1, h1.2, h2.1, h2.2]

end LipschitzDecision
