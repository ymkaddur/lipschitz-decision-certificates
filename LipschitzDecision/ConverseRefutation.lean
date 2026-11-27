import Mathlib

/-!
# Large Lipschitz bounds do not imply instability; linear layers attain their bound

Products of layer norms give sufficient conditions for stability (`MarginCertificate`,
`WeightPerturbation`). The converse fails:

* `large_bound_locally_constant` (**refutation** of "a large bound implies a nearby change of the
  output"): for every `M ≥ 0`, the one-unit ReLU layer `x ↦ max 0 (-M x)` has weight norm `M`, yet
  its output is constant on the whole interval `|r| < 1` around `x = 1`;
* `linear_bound_attained`: for a linear layer `x ↦ M x` the bound `|M| |r|` is attained for every
  perturbation, so the estimate is tight on linear layers.
-/

namespace LipschitzDecision

/-- The one-unit ReLU layer with weight `-M`. -/
noncomputable def reluUnit (M : ℝ) (x : ℝ) : ℝ := max 0 (-M * x)

/-- **Refutation of the converse.** However large `M` is, the output does not move on the
interval of radius 1 around `x = 1`, while the norm bound `M |r|` can be arbitrarily large. -/
theorem large_bound_locally_constant (M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : |r| < 1) :
    reluUnit M (1 + r) = reluUnit M 1 := by
  have hpos : 0 < 1 + r := by have := (abs_lt.mp hr).1; linarith
  unfold reluUnit
  rw [max_eq_left (by nlinarith), max_eq_left (by linarith)]

/-- The weight norm of that layer is `M`: the product-of-norms bound for a perturbation `r` is
`M |r|`, which exceeds any given `B` once `M > B / |r|`. -/
theorem norm_bound_unbounded (B r : ℝ) (hr : r ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ B < M * |r| := by
  refine ⟨(|B| + 1) / |r|, by positivity, ?_⟩
  rw [div_mul_cancel₀ _ (abs_ne_zero.mpr hr)]
  linarith [le_abs_self B]

/-- Linear layers attain the bound: `|M (x + r) - M x| = |M| |r|`. -/
theorem linear_bound_attained (M x r : ℝ) : |M * (x + r) - M * x| = |M| * |r| := by
  rw [show M * (x + r) - M * x = M * r by ring, abs_mul]

end LipschitzDecision
