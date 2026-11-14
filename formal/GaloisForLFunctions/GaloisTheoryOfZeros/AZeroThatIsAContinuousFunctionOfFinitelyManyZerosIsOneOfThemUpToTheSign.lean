import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill

/-!
# A zero that is a continuous function of finitely many zeros is one of them up to the sign

`forwardConfigurations n` is the set of the points `(τ, z₁, …, zₙ)` with `H_τ(zᵢ) = 0` for all
`i`, over the forward times `τ` off the branch times.

**Theorem** (`exists_eq_or_eq_neg_of_continuousOn_forwardConfigurations`). Let `F` be a
continuous function on the configurations whose value `F(τ, z₁, …, zₙ)` is a zero of `H_τ`. Then
at every configuration the value is `zᵢ` or `−zᵢ` for some `i`.

So no zero of the heat family is determined, continuously in the time, by finitely many other
zeros: the zeros are independent over the base up to the functional equation. For `n = 0` no
zero is a continuous function of the time; for `n = 1` the value is `±z`. The mirror statement
(`exists_eq_conj_or_eq_neg_conj_of_continuousOn_forwardConfigurations`): a zero of `H_τ̄` that is
a continuous function of the configuration is `z̄ᵢ` or `−z̄ᵢ`.

Proof. Let `w = F(τ, z)` lie in none of the pairs of `z₁, …, zₙ`, and let `y` be a zero in a
further pair. The forward monodromy group contains an element that carries `w` to `y` and fixes
`z₁, …, zₙ` (`IsWindowedSignedGroup.exists_apply_eq_of_fixed`). Along a loop for it the
configuration returns to itself, so `F` of the lifted configuration is a lift from `w` back to
`w`; but the lift from `w` ends at `y`.
-/

open Complex Set
open RHTower Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- The configurations of `n` zeros of `H_τ` over the forward times off the branch times. -/
def forwardConfigurations (n : ℕ) : Set (ℂ × (Fin n → ℂ)) :=
  {x | 0 < x.1.re ∧ x.1 ∉ branchTimes ∧ ∀ i, complexHeat x.1 (x.2 i) = 0}

variable {n : ℕ} {F : ℂ × (Fin n → ℂ) → ℂ}

/-- **A zero that depends continuously on `n` zeros is one of them up to the sign.** -/
theorem exists_eq_or_eq_neg_of_continuousOn_forwardConfigurations
    (hF : ContinuousOn F (forwardConfigurations n))
    (hzero : ∀ x ∈ forwardConfigurations n, complexHeat x.1 (F x) = 0) :
    ∀ x ∈ forwardConfigurations n, ∃ i, F x = x.2 i ∨ F x = -x.2 i := by
  rintro ⟨τ, z⟩ hx
  obtain ⟨hτ, hb, hz⟩ : 0 < τ.re ∧ τ ∉ branchTimes ∧ ∀ i, complexHeat τ (z i) = 0 := hx
  by_contra hcon
  have hcon' : ∀ i, F (τ, z) ≠ z i ∧ F (τ, z) ≠ -z i := fun i =>
    ⟨fun h => hcon ⟨i, Or.inl h⟩, fun h => hcon ⟨i, Or.inr h⟩⟩
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hτ hb
  -- the value as a point of the fibre, and the pairs of the configuration
  obtain ⟨w, hw⟩ : ∃ w : {u : ℂ // complexHeat τ u = 0}, w.1 = F (τ, z) :=
    ⟨⟨F (τ, z), hzero (τ, z) ⟨hτ, hb, hz⟩⟩, rfl⟩
  obtain ⟨A, hA, hA'⟩ : ∃ A : Finset ℤ, (∀ i, P.pair ⟨z i, hz i⟩ ∈ A) ∧
      ∀ m ∈ A, ∃ i, P.pair ⟨z i, hz i⟩ = m :=
    ⟨Finset.univ.image fun i => P.pair ⟨z i, hz i⟩,
      fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i), fun m hm => by
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
        exact ⟨i, hi⟩⟩
  have hwA : P.pair w ∉ A := by
    intro h
    obtain ⟨i, hi⟩ := hA' _ h
    rcases (P.pair_eq_iff ⟨z i, hz i⟩ w).mp hi with h' | h'
    · exact (hcon' i).1 (hw.symm.trans (congrArg Subtype.val h'))
    · exact (hcon' i).2 (hw.symm.trans (congrArg Subtype.val (h'.trans (hP _))))
  -- a zero in a further pair, and a loop that carries the value to it and fixes the configuration
  obtain ⟨y, hy⟩ := hG.exists_pair_not_mem (insert (P.pair w) A)
  rw [Finset.mem_insert, not_or] at hy
  obtain ⟨g, hg, hgw, hgA⟩ := hG.exists_apply_eq_of_fixed A hwA hy.2
  obtain ⟨γ, hγ, h0, h1, hT⟩ := hg
  have hlift : ∀ i, ∃ u : ℝ → ℂ, IsZeroLift γ 1 u ∧ u 0 = z i ∧ u 1 = z i := fun i => by
    have h := hT ⟨z i, hz i⟩
    rw [hgA _ (hA i)] at h
    exact h
  choose u hu hu0 hu1 using hlift
  have e0 : (fun i => u i 0) = z := funext hu0
  have e1 : (fun i => u i 1) = z := funext hu1
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, (γ s, fun i => u i s) ∈ forwardConfigurations n :=
    fun s hs => ⟨hγ.re_pos s hs, hγ.simple s hs, fun i => (hu i).zero s hs⟩
  -- the value along the lifted configuration is a lift from `w` to `w`
  have hTw : Transports γ w.1 w.1 := by
    refine ⟨fun s => F (γ s, fun i => u i s),
      ⟨hF.comp (hγ.continuousOn.prodMk (continuousOn_pi.2 fun i => (hu i).continuousOn)) hmem,
        fun s hs => hzero (γ s, fun i => u i s) (hmem s hs)⟩, ?_, ?_⟩
    · show F (γ 0, fun i => u i 0) = w.1
      rw [h0, e0, hw]
    · show F (γ 1, fun i => u i 1) = w.1
      rw [h1, e1, hw]
  have e : w = g w := Subtype.ext (hγ.transports_unique hTw (hT w))
  exact hy.1 (by rw [← hgw, ← e])

/-- **A zero of the mirror time that depends continuously on `n` zeros is the conjugate of one of
them up to the sign.** -/
theorem exists_eq_conj_or_eq_neg_conj_of_continuousOn_forwardConfigurations
    (hF : ContinuousOn F (forwardConfigurations n))
    (hzero : ∀ x ∈ forwardConfigurations n, complexHeat (starRingEnd ℂ x.1) (F x) = 0) :
    ∀ x ∈ forwardConfigurations n,
      ∃ i, F x = starRingEnd ℂ (x.2 i) ∨ F x = -starRingEnd ℂ (x.2 i) := by
  have hzero' : ∀ x ∈ forwardConfigurations n, complexHeat x.1 (starRingEnd ℂ (F x)) = 0 := by
    intro x hx
    have e : complexHeat x.1 (starRingEnd ℂ (F x)) =
        starRingEnd ℂ (complexHeat (starRingEnd ℂ x.1) (F x)) := by
      rw [complexHeat_conj, Complex.conj_conj]
    rw [e, hzero x hx, map_zero]
  intro x hx
  obtain ⟨i, h | h⟩ := exists_eq_or_eq_neg_of_continuousOn_forwardConfigurations
    (F := fun x => starRingEnd ℂ (F x)) (Complex.continuous_conj.comp_continuousOn hF) hzero' x hx
  · exact ⟨i, Or.inl (by rw [← Complex.conj_conj (F x), h])⟩
  · exact ⟨i, Or.inr (by rw [← Complex.conj_conj (F x), h, map_neg])⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
