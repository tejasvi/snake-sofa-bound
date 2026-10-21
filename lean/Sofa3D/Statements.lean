import Sofa3D.Defs

/-!
# The statements to be proved (as propositions)

Each statement is a `Prop`; the theorems of the project prove them. `dotProduct` is the standard dot product
on `Fin 3 → ℝ`.
-/

open MeasureTheory Set

namespace Sofa3D

/-- **Theorem 1.1.** For every `M > 2 + √2`, `V*(K_M) ≤ 2√2`. -/
def MainStatement : Prop :=
  ∀ M : ℝ, 2 + Real.sqrt 2 < M → Vstar M ≤ ENNReal.ofReal (2 * Real.sqrt 2)

/-- `Γ(u) = (u² + 2)/(u² − 2) + (u² + 2)/(2√2 u)` (Section 5). -/
noncomputable def Gamma (u : ℝ) : ℝ :=
  (u ^ 2 + 2) / (u ^ 2 - 2) + (u ^ 2 + 2) / (2 * Real.sqrt 2 * u)

/-- **Corollary 5.1.** For every `M ∈ (√2, 2 + √2]`, `V*(K_M) ≤ Γ(M)`. -/
def ShortStatement : Prop :=
  ∀ M : ℝ, Real.sqrt 2 < M → M ≤ 2 + Real.sqrt 2 → Vstar M ≤ ENNReal.ofReal (Gamma M)

/-- The weaker passage conditions of Remark 2.3: (i), (ii') `B_0 ⊆ K_M ∩ {y ≤ 1}` and
(iii') `B_1` meets `{y ≥ 1 + M}`. Every passage is a weak passage. -/
structure IsWeakPassage (M : ℝ) (B : Set (Fin 3 → ℝ))
    (g : unitInterval → Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ)) : Prop where
  continuous : Continuous g
  rotation : ∀ t, (g t).1 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ
  inside : ∀ t, motion (g t) '' B ⊆ corridor M
  start : motion (g 0) '' B ⊆ corridor M ∩ {p | p 1 ≤ 1}
  finish : ∃ p ∈ motion (g 1) '' B, 1 + M ≤ p 1

/-- **Theorem 1.1 for weak passages** (Remark 2.3; this is what Section 4 proves). -/
def WeakStatement : Prop :=
  ∀ (M : ℝ), 2 + Real.sqrt 2 < M → ∀ (B : Set (Fin 3 → ℝ)) g, IsBody B → IsWeakPassage M B g →
    volume B ≤ ENNReal.ofReal (2 * Real.sqrt 2)

/-- `(e, f₁, f₂)` is an orthonormal basis of `ℝ³` (for the dot product). -/
def Orthonormal3 (e f₁ f₂ : Fin 3 → ℝ) : Prop :=
  dotProduct e e = 1 ∧ dotProduct f₁ f₁ = 1 ∧ dotProduct f₂ f₂ = 1 ∧
    dotProduct e f₁ = 0 ∧ dotProduct e f₂ = 0 ∧ dotProduct f₁ f₂ = 0

/-- **Definition 3.1.** The tube `{ρ + λ e + a f₁ + b f₂ : λ ∈ ℝ, |a| ≤ 1/2, |b| ≤ 1/2}`. -/
def tube (ρ e f₁ f₂ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {p | ∃ l a b : ℝ, |a| ≤ 1 / 2 ∧ |b| ≤ 1 / 2 ∧ p = ρ + l • e + a • f₁ + b • f₂}

/-- **Lemma 3.3.** Two tubes whose axes make the angle `θ ∈ (0, π/2]`, `cos θ = |e · e'|`, meet in volume at
most `1/sin θ = 1/√(1 − (e · e')²)`. -/
def TwoTubeStatement : Prop :=
  ∀ ρ e f₁ f₂ ρ' e' f₁' f₂' : Fin 3 → ℝ, Orthonormal3 e f₁ f₂ → Orthonormal3 e' f₁' f₂' →
    |dotProduct e e'| < 1 →
    volume (tube ρ e f₁ f₂ ∩ tube ρ' e' f₁' f₂') ≤
      ENNReal.ofReal (1 / Real.sqrt (1 - (dotProduct e e') ^ 2))

/-- `S_Y(c) = [0, 1] × [0, c] × [0, 1]`. -/
def SYc (c : ℝ) : Set (Fin 3 → ℝ) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ c ∧ 0 ≤ p 2 ∧ p 2 ≤ 1}

/-- **Proposition 6.1.** For `0 < s < 1` and `c ≥ 1 + (1 + s)/√(1 − s²)`, the largest volume of
`T ∩ (S_X ∪ S_Y(c))` over tubes `T` whose axis direction `w` satisfies `|w · e_y| = s` is
`1/s + 1/√(1 − s²)`: it is an upper bound, and some tube attains it. -/
def RelaxStatement : Prop :=
  ∀ s c : ℝ, 0 < s → s < 1 → 1 + (1 + s) / Real.sqrt (1 - s ^ 2) ≤ c →
    (∀ ρ e f₁ f₂ : Fin 3 → ℝ, Orthonormal3 e f₁ f₂ → |e 1| = s →
      volume (tube ρ e f₁ f₂ ∩ (SX ∪ SYc c)) ≤ ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2))) ∧
    (∃ ρ e f₁ f₂ : Fin 3 → ℝ, Orthonormal3 e f₁ f₂ ∧ |e 1| = s ∧
      volume (tube ρ e f₁ f₂ ∩ (SX ∪ SYc c)) = ENNReal.ofReal (1 / s + 1 / Real.sqrt (1 - s ^ 2)))

/-- **Proposition 6.1, last sentence.** For `0 < s < 1`, `1/s + 1/√(1 − s²) ≥ 2√2`, with equality if and only if
`s = 1/√2`. -/
def RelaxValueStatement : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 → 2 * Real.sqrt 2 ≤ 1 / s + 1 / Real.sqrt (1 - s ^ 2) ∧
    (1 / s + 1 / Real.sqrt (1 - s ^ 2) = 2 * Real.sqrt 2 ↔ s = 1 / Real.sqrt 2)

/-- **Remark 2.3, bounded connected sets.** A bounded connected set `E` (not necessarily closed or measurable) that
passes through `K_M` has outer measure `volume E ≤ 2√2` when `M > 2 + √2`. -/
def BoundedStatement : Prop :=
  ∀ (M : ℝ), 2 + Real.sqrt 2 < M → ∀ (E : Set (Fin 3 → ℝ)) g, Bornology.IsBounded E → IsConnected E →
    IsPassage M E g → volume E ≤ ENNReal.ofReal (2 * Real.sqrt 2)

end Sofa3D
