# Compositional certificates

Status labels: **[L-known]** formalized here, mathematically known or elementary;
**[L]** formalized here, statement new in this form; **refuted** the claim is false and the
counterexample is formalized; **open** not proved.

## Statement

A *certified pair* `(J, Q)` has `J + Q` and `J - Q` positive semidefinite, that is `-J ≤ Q ≤ J` in
the Loewner order.

* Two-factor expansions:
  `J₁ ⊗ J₂ - Q₁ ⊗ Q₂ = ½ ((J₁ - Q₁) ⊗ (J₂ + Q₂) + (J₁ + Q₁) ⊗ (J₂ - Q₂))` and
  `J₁ ⊗ J₂ + Q₁ ⊗ Q₂ = ½ ((J₁ + Q₁) ⊗ (J₂ + Q₂) + (J₁ - Q₁) ⊗ (J₂ - Q₂))`.
* **Tensor closure**: if `(J₁, Q₁)` and `(J₂, Q₂)` are certified pairs, so is
  `(J₁ ⊗ J₂, Q₁ ⊗ Q₂)`. By induction, every finite tensor product of certified pairs is certified.
* **Interfaces**: if `(J_i - Q_i) K_i = 0` for both factors, then
  `(J₁ ⊗ J₂ - Q₁ ⊗ Q₂)(K₁ ⊗ K₂) = 0`.

## Motivation

Certify a composed object from certificates of its parts, at the cost of the parts, without
enumerating the composed space.

## Proof

Expand `J_i = A_i + B_i`, `Q_i = A_i - B_i` with `A_i = (J_i + Q_i)/2`, `B_i = (J_i - Q_i)/2`; both
expansions are sums of Kronecker products of positive semidefinite factors, which are positive
semidefinite (Mathlib `Matrix.PosSemidef.kronecker`).

## Counterexample

`ordinary_product_fails`: the principle does not transfer to ordinary products. With `J₁ = 1`,
`Q₁ = !![0,1;1,0]`, `J₂ = Q₂ = !![1,0;0,0]`, all four matrices `J_i ± Q_i` have nonnegative
quadratic forms, yet `J₁ J₂ - Q₁ Q₂ = !![1,0;-1,0]` is not symmetric and its quadratic form is `-1`
at `(1, 2)`. Tensor composition (independent factors) is not sequential composition.

## Sequential composition

Tensor composition multiplies independent factors. Sequential composition does not, and what
transfers is a *shared* certificate: if `P - F₁ᴴ P F₁` and `P - F₂ᴴ P F₂` are positive semidefinite
for the same `P`, so is `P - (F₁F₂)ᴴ P (F₁F₂)`, because the difference splits as
`(P - F₂ᴴPF₂) + F₂ᴴ (P - F₁ᴴPF₁) F₂`. For a positive definite `P` this says that both factors, and
hence the product, are contractions in the norm `‖x‖_P`. Separate certificates do not compose:
`A₁ = !![0,2;0,0]` and `A₂ = !![0,0;2,0]` are nilpotent, yet `A₁A₂ = !![4,0;0,0]`, so no positive
definite `P` certifies both.

## Formalization

`LipschitzDecision/CompositionalCertificates.lean`

| Status | Statement | Lean name |
|--------|-----------|-----------|
| [L-known] | two-factor expansion of the difference | `kron_sign_expansion` |
| [L-known] | two-factor expansion of the sum | `kron_sign_expansion_plus` |
| [L-known] | certified pairs are closed under Kronecker products | `certifiedPair_kron` |
| [L-known] | Kronecker product of Gram matrices is PSD | `kron_gram` |
| [L-known] | tensor difference PSD from explicit Gram certificates of the factors | `kron_psd_of_gram_certificates` |
| [L-known] | nulled interfaces survive tensor composition | `kron_interface_kernel` |
| **refuted** | "factor certificates imply a certificate of the ordinary product" | `ordinary_product_fails` |
| [L-known] | a shared certificate `P - FᵢᴴPFᵢ ⪰ 0` composes under products | `shared_lyapunov_mul` |
| **refuted** | "separately stable factors compose": nilpotent factors whose product grows like `4^k` | `stable_factors_unstable_product` |
| [L-known] | that pair has no positive definite common certificate | `no_common_certificate` |

## Limitations

* The `n`-factor statement follows by iterating `certifiedPair_kron`; it is not stated as a single
  theorem over heterogeneous index types.
* For sequential composition only the shared quadratic certificate is formalized. Commuting factors,
  simulation relations, positive cones and nonlinear stages are **open** here.

## Verification

`scripts/audit.sh` compiles every module with `#print axioms` of each theorem appended, and fails on
`sorry`, on warnings, or on axioms outside `propext`, `Classical.choice` and `Quot.sound`. Pinned
toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.
