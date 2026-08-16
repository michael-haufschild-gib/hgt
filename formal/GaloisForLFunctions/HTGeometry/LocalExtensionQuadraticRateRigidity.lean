import GaloisForLFunctions.HTGeometry.AffinePoleResidueRigidity
import GaloisForLFunctions.HTGeometry.BipartiteCrossPairRigidity

/-!
# The pole packet of a one-qubit local extension

Attaching one qubit to a simple-spectrum Hamiltonian and perturbing the new edge by `A ⊗ X`
produces, at second order, the response

`∂²ₓL(z,0) = 2 ∑_{α,β} (c_{α,0} − c_{β,1}) w_{αβ} / (z + E_α − E_β)`,

whose poles are the ordered old gaps.  A quadratic-rate identity multiplies this by an affine
function of `z` and equates it to a pole-free constant.  Every residue therefore vanishes, and
because a nonzero affine function has one root at most one ordered pair escapes.  The surviving
equalities form the crown graph, which stays connected after one deletion, so all the
coefficients coincide.

This file is the algebraic core: it takes the rational identity as data and returns the
coefficient collapse.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The off-diagonal ordered pairs of old labels: the nonzero poles of the response. -/
abbrev OrderedGapIndex (A : Type*) [DecidableEq A] := {q : A × A // q.1 ≠ q.2}

/-- The pole of one term of the second-order response, with the zero gap as an extra node. -/
def extensionPolePosition (E : A → ℂ) : Option (OrderedGapIndex A) → ℂ
  | none => 0
  | some t => E t.1.2 - E t.1.1

/-- The residue carried by one pole of the second-order response. -/
def extensionPoleResidue (u v : A → ℂ) (w : A → A → ℂ) :
    Option (OrderedGapIndex A) → ℂ
  | none => -∑ α, (u α - v α) * w α α
  | some t => -((u t.1.1 - v t.1.2) * w t.1.1 t.1.2)

omit [Fintype A] in
theorem extensionPolePosition_injective {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ)) :
    Function.Injective (extensionPolePosition (A := A) E) := by
  intro i j hij
  match i, j with
  | none, none => rfl
  | none, some t =>
      exfalso
      have h : E t.1.2 - E t.1.1 = 0 := by
        simpa [extensionPolePosition] using hij.symm
      exact t.2 (hE (sub_eq_zero.mp h)).symm
  | some t, none =>
      exfalso
      have h : E t.1.2 - E t.1.1 = 0 := by
        simpa [extensionPolePosition] using hij
      exact t.2 (hE (sub_eq_zero.mp h)).symm
  | some t, some s =>
      have h : E t.1.2 - E t.1.1 = E s.1.2 - E s.1.1 := by
        simpa [extensionPolePosition] using hij
      have := hgap t.1.1 t.1.2 s.1.1 s.1.2 t.2 s.2 h
      exact congrArg some (Subtype.ext (by simpa using this))

/-- The second-order response, written over its poles. -/
theorem extensionPole_sum_eq (E : A → ℂ) (u v : A → ℂ) (w : A → A → ℂ) (z : ℂ) :
    (∑ i, extensionPoleResidue u v w i / (extensionPolePosition E i - z))
      = ∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β) := by
  classical
  rw [Fintype.sum_option]
  have hdiag : extensionPoleResidue (A := A) u v w none
      / (extensionPolePosition (A := A) E none - z)
      = ∑ α, (u α - v α) * w α α / (z + E α - E α) := by
    simp only [extensionPoleResidue, extensionPolePosition, zero_sub]
    rw [neg_div_neg_eq, Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    ring
  have hoff : (∑ t : OrderedGapIndex A,
        extensionPoleResidue u v w (some t) / (extensionPolePosition E (some t) - z))
      = ∑ p ∈ Finset.univ.filter (fun p : A × A => ¬ p.1 = p.2),
          (u p.1 - v p.2) * w p.1 p.2 / (z + E p.1 - E p.2) := by
    rw [Finset.sum_subtype (p := fun p : A × A => ¬ p.1 = p.2)
      (Finset.univ.filter (fun p : A × A => ¬ p.1 = p.2)) (by intro x; simp)
      (fun p => (u p.1 - v p.2) * w p.1 p.2 / (z + E p.1 - E p.2))]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [extensionPoleResidue, extensionPolePosition]
    rw [neg_div]
    rw [show E t.1.2 - E t.1.1 - z = -(z + E t.1.1 - E t.1.2) from by ring, div_neg, neg_neg]
  rw [hdiag, hoff]
  have hsplit : (∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β))
      = ∑ p ∈ Finset.univ.filter (fun p : A × A => p.1 = p.2),
          (u p.1 - v p.2) * w p.1 p.2 / (z + E p.1 - E p.2)
        + ∑ p ∈ Finset.univ.filter (fun p : A × A => ¬ p.1 = p.2),
          (u p.1 - v p.2) * w p.1 p.2 / (z + E p.1 - E p.2) := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact (Fintype.sum_prod_type
      (fun p : A × A => (u p.1 - v p.2) * w p.1 p.2 / (z + E p.1 - E p.2))).symm
  have hdiagset : (Finset.univ.filter (fun p : A × A => p.1 = p.2))
      = Finset.image (fun a : A => (a, a)) Finset.univ := by
    ext ⟨p1, p2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨p1, rfl, h⟩
    · rintro ⟨a, h1, h2⟩
      rw [← h1, ← h2]
  rw [hsplit, hdiagset, Finset.sum_image (by
    intro a _ b _ hab
    exact congrArg Prod.fst hab)]

/-- The cleared numerator of the extension pole packet vanishes. -/
theorem extensionPacket_numerator_eq_zero
    (E : A → ℂ) (u v : A → ℂ) (w : A → A → ℂ) {p q cst : ℂ}
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hidentity : ∀ z ∈ S,
      (p + q * z) * (∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β)) = cst) :
    affinePolePacketNumerator (extensionPolePosition (A := A) E)
      (extensionPoleResidue u v w) p q cst = 0 := by
  classical
  have havoid' : ∀ z ∈ S, ∀ i, z ≠ extensionPolePosition (A := A) E i := by
    intro z hz i
    obtain ⟨hz0, hzgap⟩ := havoid z hz
    match i with
    | none => simpa [extensionPolePosition] using hz0
    | some t => simpa [extensionPolePosition] using hzgap t.1.1 t.1.2 t.2
  have hid : ∀ z ∈ S,
      (p + q * z) * ∑ i, extensionPoleResidue u v w i / (extensionPolePosition E i - z) = cst := by
    intro z hz
    rw [extensionPole_sum_eq E u v w z]
    exact hidentity z hz
  exact affinePolePacketNumerator_eq_zero_of_identity
    (extensionPolePosition (A := A) E) (extensionPoleResidue u v w) p q cst S hS havoid' hid

/-- **The residue at one ordered old gap.**  Either the affine multiplier vanishes at that gap or
the two layer coefficients agree through the probe weight. -/
theorem extensionPacket_residue
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    (u v : A → ℂ) (w : A → A → ℂ) {p q cst : ℂ}
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hidentity : ∀ z ∈ S,
      (p + q * z) * (∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β)) = cst)
    {α β : A} (hαβ : α ≠ β) :
    (u α - v β) * w α β * (p + q * (E β - E α)) = 0 := by
  classical
  have hnum := extensionPacket_numerator_eq_zero E u v w hS havoid hidentity
  have hZinj : Function.Injective (extensionPolePosition (A := A) E) :=
    extensionPolePosition_injective hE hgap
  have h := affinePoleResidue_eq_zero hZinj hnum (some ⟨(α, β), hαβ⟩)
  simp only [extensionPoleResidue, extensionPolePosition] at h
  have h' : -((u α - v β) * w α β) * (p + q * (E β - E α)) = 0 := h
  rcases mul_eq_zero.mp h' with h1 | h2
  · rw [neg_eq_zero] at h1
    exact mul_eq_zero_of_left h1 _
  · exact mul_eq_zero_of_right _ h2

/-- If the affine multiplier does not vanish at an ordered gap and the probe sees that gap, the
two layer coefficients agree. -/
theorem extensionPacket_eq_of_probe
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    (u v : A → ℂ) (w : A → A → ℂ) {p q cst : ℂ}
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hidentity : ∀ z ∈ S,
      (p + q * z) * (∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β)) = cst)
    {α β : A} (hαβ : α ≠ β) (hw : w α β ≠ 0) (hL : p + q * (E β - E α) ≠ 0) :
    u α = v β := by
  have h := extensionPacket_residue hE hgap u v w hS havoid hidentity hαβ
  rcases mul_eq_zero.mp h with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · exact sub_eq_zero.mp h3
    · exact absurd h4 hw
  · exact absurd h2 hL

/-- **The one-qubit extension collapse.**  A quadratic-rate identity for a one-qubit extension
forces every layer coefficient of the old spectrum to coincide. -/
theorem extensionPacket_crossPair_constant (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {w : A → A → ℂ} (hw : ∀ α β, α ≠ β → w α β ≠ 0)
    (u v : A → ℂ) {p q cst : ℂ} (hL : p ≠ 0 ∨ q ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hidentity : ∀ z ∈ S,
      (p + q * z) * (∑ α, ∑ β, (u α - v β) * w α β / (z + E α - E β)) = cst) :
    (∀ x y, u x = u y) ∧ (∀ x y, v x = v y) ∧ (∀ x y, u x = v y) := by
  classical
  have hZinj : Function.Injective (extensionPolePosition (A := A) E) :=
    extensionPolePosition_injective hE hgap
  have havoid' : ∀ z ∈ S, ∀ i, z ≠ extensionPolePosition (A := A) E i := by
    intro z hz i
    obtain ⟨hz0, hzgap⟩ := havoid z hz
    match i with
    | none => simpa [extensionPolePosition] using hz0
    | some t => simpa [extensionPolePosition] using hzgap t.1.1 t.1.2 t.2
  have hid : ∀ z ∈ S,
      (p + q * z) * ∑ i, extensionPoleResidue u v w i / (extensionPolePosition E i - z) = cst := by
    intro z hz
    rw [extensionPole_sum_eq E u v w z]
    exact hidentity z hz
  have hnum := affinePolePacketNumerator_eq_zero_of_identity
    (extensionPolePosition (A := A) E) (extensionPoleResidue u v w) p q cst S hS havoid' hid
  have hsub := affinePole_support_subsingleton hZinj hL hnum
  -- the exceptional ordered pair, if any
  obtain ⟨a₀⟩ : Nonempty A := by
    rw [← Fintype.card_pos_iff]
    omega
  set exc : A × A :=
    if h : ∃ t : OrderedGapIndex A, extensionPoleResidue u v w (some t) ≠ 0 then
      (Classical.choose h).1 else (a₀, a₀) with hexc
  have hkey : ∀ x y : A, x ≠ y → (x, y) ≠ exc → u x = v y := by
    intro x y hxy hne
    have hres : extensionPoleResidue u v w (some ⟨(x, y), hxy⟩) = 0 := by
      by_contra hcon
      have hex : ∃ t : OrderedGapIndex A, extensionPoleResidue u v w (some t) ≠ 0 :=
        ⟨⟨(x, y), hxy⟩, hcon⟩
      have hspec := Classical.choose_spec hex
      have heq := hsub (some (Classical.choose hex)) (some ⟨(x, y), hxy⟩) hspec hcon
      apply hne
      rw [hexc, dif_pos hex]
      exact congrArg Subtype.val (Option.some_injective _ heq).symm
    have hzero : (u x - v y) * w x y = 0 := by
      have := hres
      simp only [extensionPoleResidue, neg_eq_zero] at this
      exact this
    rcases mul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (hw x y hxy)
  exact crossPair_constant hcard u v exc hkey

/-- **The extension collapse for a family of probes.**  The affine multiplier is the same for
every probe, so at most one ordered gap is exceptional; a probe family that sees every ordered pair
therefore collapses all layer coefficients. -/
theorem extensionKey_family_collapse (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {P : Type*} {w : P → A → A → ℂ}
    (hcover : ∀ α β : A, α ≠ β → ∃ s, w s α β ≠ 0)
    (u v : A → ℂ) {p q : ℂ} {cst : P → ℂ} (hL : p ≠ 0 ∨ q ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hkey : ∀ s : P, ∀ z ∈ S,
      (p + q * z) * (∑ α, ∑ β, (u α - v β) * w s α β / (z + E α - E β)) = cst s) :
    (∀ x y, u x = u y) ∧ (∀ x y, v x = v y) ∧ (∀ x y, u x = v y) := by
  classical
  obtain ⟨a₀⟩ : Nonempty A := by
    rw [← Fintype.card_pos_iff]
    omega
  set exc : A × A :=
    if h : ∃ t : OrderedGapIndex A, p + q * (E t.1.2 - E t.1.1) = 0 then
      (Classical.choose h).1 else (a₀, a₀) with hexc
  have hne : ∀ α β : A, α ≠ β → (α, β) ≠ exc → p + q * (E β - E α) ≠ 0 := by
    intro α β hαβ hpair hzero
    have hex : ∃ t : OrderedGapIndex A, p + q * (E t.1.2 - E t.1.1) = 0 :=
      ⟨⟨(α, β), hαβ⟩, hzero⟩
    have hspec := Classical.choose_spec hex
    set t₀ := Classical.choose hex with ht₀
    have hq : q ≠ 0 := by
      rcases hL with hp | hq
      · intro hq0
        rw [hq0, zero_mul, add_zero] at hzero
        exact hp hzero
      · exact hq
    have hgapeq : E β - E α = E t₀.1.2 - E t₀.1.1 := by
      have h1 : q * (E β - E α) = -p := by linear_combination hzero
      have h2 : q * (E t₀.1.2 - E t₀.1.1) = -p := by linear_combination hspec
      exact mul_left_cancel₀ hq (by rw [h1, h2])
    apply hpair
    rw [hexc, dif_pos hex]
    exact (hgap α β t₀.1.1 t₀.1.2 hαβ t₀.2 hgapeq)
  have hcross : ∀ x y : A, x ≠ y → (x, y) ≠ exc → u x = v y := by
    intro x y hxy hpair
    obtain ⟨s, hs⟩ := hcover x y hxy
    exact extensionPacket_eq_of_probe hE hgap u v (w s) hS havoid (hkey s) hxy hs
      (hne x y hxy hpair)
  exact crossPair_constant hcard u v exc hcross

end

end GaloisForLFunctions.HTGeometry
