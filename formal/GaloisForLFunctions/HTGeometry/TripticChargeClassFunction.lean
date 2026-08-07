import GaloisForLFunctions.HTGeometry.TripticSourceDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The orbital charge is a class function on the period group

The triptic orbital charge is attached to a base point, but it depends only on that point's class
in the period group `H₃ = ℤ + ℤτ + ℤσ`, which is what makes it a divisor on `G = ℂ/H₃`.

Invariance in the three directions has three different reasons.

* Along `σ` it is invariance of a telescoping sum under reindexing.
* Along `1` it is `1`-periodicity of the source, which moves every order.
* Along `τ` it is the mixed-cocycle condition: the shift quotient `A_σ = Y(·+σ)/Y` satisfies
  `A_σ(z + τ) = C_Y(z) A_σ(z)` with `C_Y` an exponential character, so its divisor is
  `τ`-invariant.

The first two are proved here outright; the third is the exact translation of the cocycle condition
into a statement about orders.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- A period of a function is a period of its meromorphic order. -/
theorem meromorphicOrderAt_of_period {Y : ℂ → ℂ} {p : ℂ} (hper : ∀ z, Y (z + p) = Y z) (x : ℂ) :
    meromorphicOrderAt Y (x + p) = meromorphicOrderAt Y x := by
  have hfun : (fun z => Y (z + p)) = Y := funext hper
  have h := meromorphicOrderAt_comp_add Y x p
  rw [hfun] at h
  exact h.symm

/-- A period of the source is a period of every shift order. -/
theorem shiftOrder_of_period {Y : ℂ → ℂ} {σ p : ℂ} (hper : ∀ z, Y (z + p) = Y z) (w : ℂ) :
    shiftOrder Y σ (w + p) = shiftOrder Y σ w := by
  rw [shiftOrder, shiftOrder, show w + p + σ = (w + σ) + p by ring,
    meromorphicOrderAt_of_period hper, meromorphicOrderAt_of_period hper]

/-- **The orbital charge is invariant under a period of the source.**  In particular it is
`1`-invariant for every member of the triptic source class. -/
theorem tripticOrbitCharge_of_period {Y : ℂ → ℂ} {σ p q : ℂ} (hper : ∀ z, Y (z + p) = Y z) :
    tripticOrbitCharge Y σ (q + p) = tripticOrbitCharge Y σ q := by
  rw [tripticOrbitCharge, tripticOrbitCharge]
  refine finsum_congr fun m => ?_
  rw [show q + p + (m : ℂ) * σ = (q + (m : ℂ) * σ) + p by ring, shiftOrder_of_period hper]

/-- **The orbital charge is `τ`-invariant when the shift-quotient divisor is.**  This is the exact
content of the mixed-cocycle condition: multiplying the shift quotient by a nowhere-zero,
nowhere-polar exponential character leaves every order unchanged. -/
theorem tripticOrbitCharge_of_shiftOrder_invariant {Y : ℂ → ℂ} {σ τ q : ℂ}
    (hinv : ∀ w : ℂ, shiftOrder Y σ (w + τ) = shiftOrder Y σ w) :
    tripticOrbitCharge Y σ (q + τ) = tripticOrbitCharge Y σ q := by
  rw [tripticOrbitCharge, tripticOrbitCharge]
  refine finsum_congr fun m => ?_
  rw [show q + τ + (m : ℂ) * σ = (q + (m : ℂ) * σ) + τ by ring, hinv]

/-- Invariance under one period upgrades to invariance under all its integer multiples. -/
theorem eq_of_add_zsmul {f : ℂ → ℤ} {p : ℂ} (h : ∀ r : ℂ, f (r + p) = f r) (r : ℂ) (n : ℤ) :
    f (r + (n : ℂ) * p) = f r := by
  induction n using Int.induction_on with
  | zero => norm_num
  | succ k ih =>
      have hs : r + (((k : ℤ) + 1 : ℤ) : ℂ) * p = (r + ((k : ℤ) : ℂ) * p) + p := by
        push_cast; ring
      rw [hs, h, ih]
  | pred k ih =>
      have hs : (r + ((-(k : ℤ) - 1 : ℤ) : ℂ) * p) + p = r + ((-(k : ℤ) : ℤ) : ℂ) * p := by
        push_cast; ring
      have hh := h (r + ((-(k : ℤ) - 1 : ℤ) : ℂ) * p)
      rw [hs] at hh
      rw [← hh, ih]

/-- **The orbital charge is a class function on the full period group.**  Translating the base
point by any element of `ℤ + ℤτ + ℤσ` leaves the charge unchanged. -/
theorem tripticOrbitCharge_of_periodGroup {Y : ℂ → ℂ} {σ τ q : ℂ}
    (hone : ∀ z, Y (z + 1) = Y z)
    (hinv : ∀ w : ℂ, shiftOrder Y σ (w + τ) = shiftOrder Y σ w)
    (hsig : ∀ r : ℂ, tripticOrbitCharge Y σ (r + σ) = tripticOrbitCharge Y σ r)
    (c d e : ℤ) :
    tripticOrbitCharge Y σ (q + (c : ℂ) * 1 + (d : ℂ) * τ + (e : ℂ) * σ)
      = tripticOrbitCharge Y σ q := by
  have hcharge := fun r : ℂ => tripticOrbitCharge_of_period (Y := Y) (σ := σ) (p := 1) (q := r) hone
  have htau := fun r : ℂ =>
    tripticOrbitCharge_of_shiftOrder_invariant (Y := Y) (σ := σ) (τ := τ) (q := r) hinv
  rw [eq_of_add_zsmul hsig _ e, eq_of_add_zsmul htau _ d, eq_of_add_zsmul hcharge _ c]

/-! ### Local finiteness of the charge support -/

/-- An order that is not `⊤` and untops to `0` is `0`. -/
theorem meromorphicOrderAt_eq_zero_of_untop₀ {Y : ℂ → ℂ} {z : ℂ}
    (hne : meromorphicOrderAt Y z ≠ ⊤) (h0 : (meromorphicOrderAt Y z).untop₀ = 0) :
    meromorphicOrderAt Y z = 0 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at h0 ⊢
  simp only [WithTop.untop₀_coe] at h0
  exact_mod_cast h0

/-- **The divisor of a meromorphic function meets every compact set finitely.** -/
theorem finite_setOf_meromorphicOrderAt_ne_zero {Y : ℂ → ℂ} (hY : MeromorphicOn Y Set.univ)
    (hne : ∀ z, meromorphicOrderAt Y z ≠ ⊤) {K : Set ℂ} (hK : IsCompact K) :
    {z | z ∈ K ∧ meromorphicOrderAt Y z ≠ 0}.Finite := by
  have hYK : MeromorphicOn Y K := fun z _ => hY z (Set.mem_univ z)
  refine ((MeromorphicOn.divisor Y K).finiteSupport hK).subset ?_
  rintro z ⟨hzK, hz0⟩
  have hval : (MeromorphicOn.divisor Y K) z = (meromorphicOrderAt Y z).untop₀ :=
    MeromorphicOn.divisor_apply hYK hzK
  simp only [Function.mem_support, hval]
  intro hz
  exact hz0 (meromorphicOrderAt_eq_zero_of_untop₀ (hne z) hz)

/-- **The shift-order support meets every compact set finitely.**  A base point can only carry
charge if the source has a zero or pole at it or at its `σ`-translate, and each of those sets is
finite on a compact region. -/
theorem finite_setOf_shiftOrder_ne_zero {Y : ℂ → ℂ} {σ : ℂ} (hY : MeromorphicOn Y Set.univ)
    (hne : ∀ z, meromorphicOrderAt Y z ≠ ⊤) {K : Set ℂ} (hK : IsCompact K) :
    {w | w ∈ K ∧ shiftOrder Y σ w ≠ 0}.Finite := by
  have hKs : IsCompact ((fun w : ℂ => w + σ) '' K) := hK.image (by fun_prop)
  have h1 := finite_setOf_meromorphicOrderAt_ne_zero hY hne hK
  have h2 := finite_setOf_meromorphicOrderAt_ne_zero hY hne hKs
  have h2' : {w | w ∈ K ∧ meromorphicOrderAt Y (w + σ) ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun w : ℂ => w + σ) (h2.subset ?_) ?_
    · rintro y ⟨w, ⟨hwK, hw0⟩, rfl⟩
      exact ⟨⟨w, hwK, rfl⟩, hw0⟩
    · exact fun x _ y _ h => by simpa using h
  refine (h1.union h2').subset ?_
  rintro w ⟨hwK, hw0⟩
  by_cases hz : meromorphicOrderAt Y w = 0
  · refine Or.inr ⟨hwK, ?_⟩
    intro hzs
    exact hw0 (by rw [shiftOrder, hzs, hz]; simp)
  · exact Or.inl ⟨hwK, hz⟩

end GaloisForLFunctions.HTGeometry
