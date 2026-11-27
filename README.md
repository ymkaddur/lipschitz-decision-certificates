# lipschitz-decision-certificates

Machine-checked certificates that a classifier's decision survives input or weight perturbations,
together with a proof that the converse fails, in Lean 4 with Mathlib.

Norm bounds of the form `‖φ(x) − φ(x + r)‖ ≤ (∏ ‖W_k‖) ‖r‖` give sufficient conditions for stable
decisions: small bounds rule out nearby changes of the decision. This repository proves these
certificates for input perturbations and for weight perturbations (for example, quantized weights),
with an explicit per-layer error budget. It also proves that large bounds do **not** imply that the
output changes nearby.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Labels: **[L]** new theorem or construction proved in Lean; **[L-known]** Lean formalization of a known result; **refuted** counterexample proved in Lean; **open** precise statement not resolved here.

## Contents

| Module | Statement | Status |
|--------|-----------|--------|
| `MarginCertificate` | `‖u − v‖∞ ≤ ε` and a top-1 margin `> 2ε` keep the top-1 class; same for top-k sets | [L-known] |
| | Lipschitz logits: margin `> 2L‖r‖` at `x` certifies the decision at `x + r` | [L-known] |
| | linear head `z_j = ⟨w_j, x⟩`: the pairwise certificate `⟨w_i − w_j, x⟩ > ‖w_i − w_j‖ ‖r‖` suffices | [L-known] |
| `WeightPerturbation` | network `x_(k+1) = σ(W_k x_k)` with `σ` 1-Lipschitz, `σ(0) = 0`, no bias: `‖x_K‖ ≤ (∏ ‖W_j‖) ‖x‖` | [L-known] |
| | telescoping bound `‖φ(x;W) − φ(x;Ŵ)‖ ≤ ∑_k (∏_(j>k) ‖W_j‖) ‖W_k − Ŵ_k‖ (∏_(j<k) ‖Ŵ_j‖) ‖x‖` | [L-known] |
| | per-layer error budget: a budget below half the margin preserves the top-1 class | [L] |
| `ConverseRefutation` | claim "a large norm bound implies a nearby change of the output": the ReLU unit `max(0, −M x)` has weight `M` (arbitrarily large) but is constant on `|r| < 1` around `x = 1` | **refuted** |
| | for any `B` and `r ≠ 0` some weight `M` makes the bound `M |r|` exceed `B` | [L-known] |
| | linear layers attain the bound: `|M(x + r) − M x| = |M| |r|` | [L-known] |

Open questions:

- **open**: certificates that use the activation pattern, which only certify the region where
  ReLU signs are fixed and can be far tighter than products of norms.
- **open**: the minimum per-layer precision (bits) that satisfies the weight budget for a given margin
  distribution.

## Reproduce

```bash
lake exe cache get
lake build
scripts/audit.sh     # #print axioms for every theorem; fails on sorry, warnings or extra axioms
```

Pinned toolchain: `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`).

## Related work

The layer-wise Lipschitz analysis of deep networks, and the remark that large bounds do not by
themselves imply adversarial examples, appear in C. Szegedy et al., *Intriguing properties of neural
networks* (arXiv:1312.6199). This repository proves formal versions independently.

## License

MIT
