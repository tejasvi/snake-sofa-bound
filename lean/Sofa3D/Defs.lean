import Mathlib

/-!
# The three-dimensional sofa problem in a snake-shaped corridor: definitions

Points of `ℝ³` are functions `p : Fin 3 → ℝ`, with `p 0 = x`, `p 1 = y`, `p 2 = z`. Volume is Mathlib's
Lebesgue measure `MeasureTheory.volume` on `Fin 3 → ℝ` (the product of the Lebesgue measures).
Definitions 2.1 and 2.2 of the paper.
-/

open MeasureTheory Set

namespace Sofa3D

/-- The entry arm `S_X = (-∞, 0] × [0, 1] × [0, 1]`. -/
def SX : Set (Fin 3 → ℝ) := {p | p 0 ≤ 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

/-- The middle arm `S_Y = [0, 1] × [0, 1 + M] × [0, 1]`. -/
def SY (M : ℝ) : Set (Fin 3 → ℝ) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 + M ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

/-- The exit arm `S_Z = [0, 1] × [1 + M, 2 + M] × [0, ∞)`. -/
def SZ (M : ℝ) : Set (Fin 3 → ℝ) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 1 + M ≤ p 1 ∧ p 1 ≤ 2 + M ∧ 0 ≤ p 2}

/-- The corridor `K_M = S_X ∪ S_Y ∪ S_Z` (Definition 2.1). -/
def corridor (M : ℝ) : Set (Fin 3 → ℝ) := SX ∪ SY M ∪ SZ M

/-- A body: a nonempty compact connected set (`IsConnected` includes nonemptiness). -/
def IsBody (B : Set (Fin 3 → ℝ)) : Prop := IsCompact B ∧ IsConnected B

/-- The rigid motion `p ↦ R p + v` given by a pair `g = (R, v)`. -/
def motion (g : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Matrix.mulVec g.1 p + g.2

/-- A passage of `B` through `K_M` (Definition 2.2): a continuous map `t ↦ g_t = (R_t, v_t)` from
`[0, 1]` to `SE(3) ⊆ ℝ^{3×3} × ℝ³` with `g_t(B) ⊆ K_M` for all `t`, `g_0(B) ⊆ S_X` and `g_1(B) ⊆ S_Z`. -/
structure IsPassage (M : ℝ) (B : Set (Fin 3 → ℝ))
    (g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) : Prop where
  continuous : Continuous g
  rotation : ∀ t, (g t).1 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ
  inside : ∀ t, motion (g t) '' B ⊆ corridor M
  start : motion (g 0) '' B ⊆ SX
  finish : motion (g 1) '' B ⊆ SZ M

/-- `V*(K_M)`: the supremum of `vol B` over all bodies `B` that have a passage through `K_M`. -/
noncomputable def Vstar (M : ℝ) : ENNReal :=
  ⨆ (B : Set (Fin 3 → ℝ)) (_ : IsBody B) (_ : ∃ g, IsPassage M B g), volume B

end Sofa3D
