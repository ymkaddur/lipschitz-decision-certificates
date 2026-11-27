import Mathlib

/-!
# Margin certificates for decisions under input perturbations

Logits live in `ι → ℝ` with the sup norm.

* `top1_of_close`: if `‖u - v‖ ≤ ε` and the top class of `u` leads every competitor by more than
  `2ε`, it is still the strict top class of `v`;
* `top1_of_lipschitz`: if the logit map `φ` satisfies `‖φ (x + r) - φ x‖ ≤ L ‖r‖`, a margin larger
  than `2 L ‖r‖` at `x` certifies the decision at `x + r`;
* `topk_of_close`: the same for a top set `S`;
* `top1_linear_contrast`: for a linear head `z_j(x) = ⟪w_j, x⟫`, the pairwise certificate
  `⟪w_i - w_j, x⟫ > ‖w_i - w_j‖ ‖r‖` suffices. It never needs more than the per-row certificate, and
  it ignores any component common to all rows.
-/

namespace LipschitzDecision

/-- Closeness in sup norm plus a margin of `2ε` preserves the top-1 class. -/
theorem top1_of_close {ι : Type*} [Fintype ι] (u v : ι → ℝ) (ε : ℝ) (h : ‖u - v‖ ≤ ε) (i : ι)
    (hm : ∀ j, j ≠ i → u j + 2 * ε < u i) : ∀ j, j ≠ i → v j < v i := by
  have hc : ∀ k, |u k - v k| ≤ ε := fun k => by
    have := norm_le_pi_norm (u - v) k
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  intro j hj
  have h1 := abs_le.mp (hc j)
  have h2 := abs_le.mp (hc i)
  have := hm j hj
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The same for a top set `S`: every member stays above every non-member. -/
theorem topk_of_close {ι : Type*} [Fintype ι] (u v : ι → ℝ) (ε : ℝ) (h : ‖u - v‖ ≤ ε)
    (S : Set ι) (hm : ∀ i ∈ S, ∀ j ∉ S, u j + 2 * ε < u i) : ∀ i ∈ S, ∀ j ∉ S, v j < v i := by
  have hc : ∀ k, |u k - v k| ≤ ε := fun k => by
    have := norm_le_pi_norm (u - v) k
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  intro i hi j hj
  have h1 := abs_le.mp (hc j)
  have h2 := abs_le.mp (hc i)
  have := hm i hi j hj
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- Lipschitz certificate: a margin larger than `2 L ‖r‖` at `x` preserves the top-1 at `x + r`. -/
theorem top1_of_lipschitz {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (φ : E → ι → ℝ)
    (L : ℝ) (x r : E) (hφ : ‖φ (x + r) - φ x‖ ≤ L * ‖r‖) (i : ι)
    (hm : ∀ j, j ≠ i → φ x j + 2 * (L * ‖r‖) < φ x i) :
    ∀ j, j ≠ i → φ (x + r) j < φ (x + r) i :=
  top1_of_close (φ x) (φ (x + r)) (L * ‖r‖) (by rw [norm_sub_rev]; exact hφ) i hm

/-- Pairwise certificate for a linear head `z_j(x) = ⟪w_j, x⟫`. -/
theorem top1_linear_contrast {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → E) (x r : E) (i : ι) (h : ∀ j, j ≠ i → ‖w i - w j‖ * ‖r‖ < inner ℝ (w i - w j) x) :
    ∀ j, j ≠ i → inner ℝ (w j) (x + r) < inner ℝ (w i) (x + r) := by
  intro j hj
  have hcs : |inner ℝ (w i - w j) r| ≤ ‖w i - w j‖ * ‖r‖ := abs_real_inner_le_norm _ _
  have hsplit : inner ℝ (w i) (x + r) - inner ℝ (w j) (x + r) =
      inner ℝ (w i - w j) x + inner ℝ (w i - w j) r := by
    simp only [inner_add_right, inner_sub_left]; ring
  have := h j hj
  have := (abs_le.mp hcs).1
  linarith

end LipschitzDecision
