import Mathlib.Topology.MetricSpace.Lipschitz

/-! State-dependent selection of individually compatible actions. -/
namespace LipschitzDecision.SwitchedReaders

/-- Exact switched dynamics need only agree on the actions selected on each observation fiber. -/
theorem switched_iff {X Y A : Type*} [Nonempty Y] (view : X → Y) (key : X → A)
    (act : A → X → X) (reduced : A → Y → Y)
    (law : ∀ a x, view (act a x) = reduced a (view x)) :
    (∃ g : Y → Y, ∀ x, view (act (key x) x) = g (view x)) ↔
    ∀ x y, view x = view y → reduced (key x) (view x) = reduced (key y) (view y) := by
  classical
  constructor
  · rintro ⟨g,h⟩ x y he
    rw [← law, ← law, h, h, he]
  · intro h
    let g (y : Y) := if hy : ∃ x, view x = y then reduced (key hy.choose) y else Classical.arbitrary Y
    refine ⟨g, fun x => ?_⟩
    have hx : ∃ z, view z = view x := ⟨x,rfl⟩
    rw [law]
    simp only [g, dif_pos hx]
    simpa only [hx.choose_spec] using h x hx.choose hx.choose_spec.symm

/-- A difference in selected controls contributes an additional term even for Lipschitz actions. -/
theorem switched_dist {X A : Type*} [PseudoMetricSpace X] (act : A → X → X) (L : NNReal)
    (h : ∀ a, LipschitzWith L (act a)) (a b : A) (x y : X) :
    dist (act a x) (act b y) ≤ L * dist x y + dist (act a y) (act b y) :=
  (dist_triangle _ (act a y) _).trans (add_le_add ((h a).dist_le_mul x y) le_rfl)

/-- Identity and negation preserve the public bit separately. A hidden selector breaks closure. -/
theorem hidden_selector :
    ¬ ∃ g : Bool → Bool, ∀ x : Bool × Bool, (if x.2 then !x.1 else x.1) = g x.1 := by
  rintro ⟨g,h⟩
  have h₀ := h (false,false)
  have h₁ := h (false,true)
  simp at h₀ h₁
  exact Bool.noConfusion (h₀.symm.trans h₁)

end LipschitzDecision.SwitchedReaders
