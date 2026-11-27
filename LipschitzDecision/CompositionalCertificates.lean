import Mathlib

/-!
# Compositional certificates: tensor sign expansion versus ordinary products

For factors `J_i, Q_i`, with `A_i = (J_i + Q_i)/2` and `B_i = (J_i - Q_i)/2`, two factors expand as

`J₁ ⊗ J₂ - Q₁ ⊗ Q₂ = ½ ((J₁ - Q₁) ⊗ (J₂ + Q₂) + (J₁ + Q₁) ⊗ (J₂ - Q₂))`   (`kron_sign_expansion`).

* `kron_gram`: the Kronecker product of two Gram matrices is a Gram matrix,
  `(Lᴴ L) ⊗ (Mᴴ M) = (L ⊗ M)ᴴ (L ⊗ M)`, hence positive semidefinite;
* `kron_psd_of_gram_certificates`: if each factor certificate is given in Gram form,
  `J_i - Q_i = L_iᴴ L_i` and `J_i + Q_i = M_iᴴ M_i`, then `J₁ ⊗ J₂ - Q₁ ⊗ Q₂` is positive semidefinite.
  Every real PSD matrix has such a factorization (spectral theorem), which is not re-proved here;
  the hypothesis is the computational certificate one actually stores;
* `kron_interface_kernel`: if `(J_i - Q_i) K_i = 0` for both factors, then
  `(J₁ ⊗ J₂ - Q₁ ⊗ Q₂)(K₁ ⊗ K₂) = 0`. A nulled interface survives tensor composition;
* `kron_sign_expansion_plus`, `certifiedPair_kron`: a *certified pair* has `J + Q` and `J - Q`
  positive semidefinite. Certified pairs are closed under Kronecker products, so by induction on
  the number of factors every finite tensor product of certified pairs is certified;
* `ordinary_product_fails` (**refutation**): the principle does not transfer to ordinary products.
  There are `J_i ± Q_i` with nonnegative quadratic forms for which `J₁ J₂ - Q₁ Q₂` is neither
  symmetric nor nonnegative.
-/

namespace LipschitzDecision.Compositional

open Matrix Kronecker

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] [Fintype n] in
/-- Two-factor sign expansion. -/
theorem kron_sign_expansion (J₁ Q₁ : Matrix m m ℝ) (J₂ Q₂ : Matrix n n ℝ) :
    J₁ ⊗ₖ J₂ - Q₁ ⊗ₖ Q₂ =
      ((1 : ℝ) / 2) • ((J₁ - Q₁) ⊗ₖ (J₂ + Q₂) + (J₁ + Q₁) ⊗ₖ (J₂ - Q₂)) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, kronecker_apply, smul_eq_mul]
  ring

/-- The Kronecker product of Gram matrices is a Gram matrix, hence PSD. -/
theorem kron_gram {p q : Type*} [Fintype p] [Fintype q] (L : Matrix p m ℝ) (M : Matrix q n ℝ) :
    ((Lᴴ * L) ⊗ₖ (Mᴴ * M)).PosSemidef := by
  rw [mul_kronecker_mul, ← conjTranspose_kronecker]
  exact posSemidef_conjTranspose_mul_self _

/-- **Positivity of the tensor difference** from Gram certificates of the factors. -/
theorem kron_psd_of_gram_certificates {p₁ q₁ p₂ q₂ : Type*} [Fintype p₁] [Fintype q₁]
    [Fintype p₂] [Fintype q₂] (J₁ Q₁ : Matrix m m ℝ) (J₂ Q₂ : Matrix n n ℝ)
    (L₁ : Matrix p₁ m ℝ) (M₁ : Matrix q₁ m ℝ) (L₂ : Matrix p₂ n ℝ) (M₂ : Matrix q₂ n ℝ)
    (h₁m : J₁ - Q₁ = L₁ᴴ * L₁) (h₁p : J₁ + Q₁ = M₁ᴴ * M₁)
    (h₂m : J₂ - Q₂ = L₂ᴴ * L₂) (h₂p : J₂ + Q₂ = M₂ᴴ * M₂) :
    (J₁ ⊗ₖ J₂ - Q₁ ⊗ₖ Q₂).PosSemidef := by
  rw [kron_sign_expansion, h₁m, h₁p, h₂m, h₂p]
  exact ((kron_gram L₁ M₂).add (kron_gram M₁ L₂)).smul (by norm_num)

/-- **Nulled interfaces survive tensor composition.** -/
theorem kron_interface_kernel {p q : Type*} [Fintype p] [Fintype q] (J₁ Q₁ : Matrix m m ℝ)
    (J₂ Q₂ : Matrix n n ℝ) (K₁ : Matrix m p ℝ) (K₂ : Matrix n q ℝ)
    (h₁ : (J₁ - Q₁) * K₁ = 0) (h₂ : (J₂ - Q₂) * K₂ = 0) :
    (J₁ ⊗ₖ J₂ - Q₁ ⊗ₖ Q₂) * (K₁ ⊗ₖ K₂) = 0 := by
  rw [kron_sign_expansion, Matrix.smul_mul, Matrix.add_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, h₁, h₂, zero_kronecker, kronecker_zero, add_zero, smul_zero]

omit [Fintype m] [Fintype n] in
/-- Two-factor expansion of the sum. -/
theorem kron_sign_expansion_plus (J₁ Q₁ : Matrix m m ℝ) (J₂ Q₂ : Matrix n n ℝ) :
    J₁ ⊗ₖ J₂ + Q₁ ⊗ₖ Q₂ =
      ((1 : ℝ) / 2) • ((J₁ + Q₁) ⊗ₖ (J₂ + Q₂) + (J₁ - Q₁) ⊗ₖ (J₂ - Q₂)) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, kronecker_apply, smul_eq_mul]
  ring

/-- A certified pair: `J + Q` and `J - Q` are positive semidefinite (`-J ≤ Q ≤ J` in the Loewner
order). -/
def CertifiedPair (J Q : Matrix m m ℝ) : Prop := (J + Q).PosSemidef ∧ (J - Q).PosSemidef

/-- **Tensor closure**: certified pairs are closed under Kronecker products. Iterating gives the
statement for any finite number of factors. -/
theorem certifiedPair_kron {J₁ Q₁ : Matrix m m ℝ} {J₂ Q₂ : Matrix n n ℝ}
    (h₁ : CertifiedPair J₁ Q₁) (h₂ : CertifiedPair J₂ Q₂) :
    CertifiedPair (J₁ ⊗ₖ J₂) (Q₁ ⊗ₖ Q₂) := by
  refine ⟨?_, ?_⟩
  · rw [kron_sign_expansion_plus]
    exact ((h₁.1.kronecker h₂.1).add (h₁.2.kronecker h₂.2)).smul (by norm_num)
  · rw [kron_sign_expansion]
    exact ((h₁.2.kronecker h₂.1).add (h₁.1.kronecker h₂.2)).smul (by norm_num)

/-- **Refutation for ordinary products.** -/
theorem ordinary_product_fails :
    let J₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
    let Q₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let J₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let Q₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    (∀ x : Fin 2 → ℝ, 0 ≤ x ⬝ᵥ ((J₁ + Q₁) *ᵥ x) ∧ 0 ≤ x ⬝ᵥ ((J₁ - Q₁) *ᵥ x) ∧
        0 ≤ x ⬝ᵥ ((J₂ + Q₂) *ᵥ x) ∧ 0 ≤ x ⬝ᵥ ((J₂ - Q₂) *ᵥ x)) ∧
      (J₁ * J₂ - Q₁ * Q₂)ᵀ ≠ J₁ * J₂ - Q₁ * Q₂ ∧
      ![1, 2] ⬝ᵥ ((J₁ * J₂ - Q₁ * Q₂) *ᵥ ![1, 2]) = -1 := by
  intro J₁ Q₁ J₂ Q₂
  have e1 : J₁ + Q₁ = !![1, 1; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J₁, Q₁]
  have e2 : J₁ - Q₁ = !![1, -1; -1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J₁, Q₁]
  have e3 : J₂ + Q₂ = !![2, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [J₂, Q₂]
  have e4 : J₂ - Q₂ = !![0, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J₂, Q₂]
  have e5 : J₁ * J₂ - Q₁ * Q₂ = !![1, 0; -1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J₁, Q₁, J₂, Q₂]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [e1, e2, e3, e4]
    simp only [dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    refine ⟨by nlinarith [sq_nonneg (x 0 + x 1)], by nlinarith [sq_nonneg (x 0 - x 1)],
      by nlinarith [sq_nonneg (x 0)], by nlinarith⟩
  · rw [e5]
    intro h
    have := congrFun (congrFun h 0) 1
    simp at this
  · rw [e5]
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    norm_num

end LipschitzDecision.Compositional
