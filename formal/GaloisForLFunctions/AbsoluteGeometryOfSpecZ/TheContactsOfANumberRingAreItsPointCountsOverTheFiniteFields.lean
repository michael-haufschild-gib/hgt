import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# The contacts of a number ring are its point counts over the finite fields

Let `K` be a number field. Counted by norms, the contact order of the norm `n` on the square of
its ring of integers is `Σ_{N𝔭^k = n} log N𝔭` (`idealContact`).

* **Point counts** (`idealContact_prime_pow`). Let `a_d(p)` be the number of prime ideals of
  norm `p^d`, the closed points of degree `d` of the fibre over `p`. Then

    `idealContact(p^m) = N_m(p) log p`,  `N_m(p) = Σ_{d ∣ m} d a_d(p)`  (`fibrePointCount`).

  The contact order vanishes at every norm that is not a prime power (`idealContact_eq_zero`).
* **The points of the fibre** (`natCard_ringHom_eq_fibrePointCount`,
  `idealContact_prime_pow_eq_natCard_ringHom`). `N_m(p)` is the number of ring homomorphisms
  from the ring of integers into a field with `p^m` elements. A homomorphism is its kernel `𝔭`,
  a prime ideal of norm `p^d`, and an embedding of the residue field; a field with `p^d`
  elements embeds into a field with `p^m` elements only if `d ∣ m`, and then in `d` ways
  (`ringHom_finiteField`).
* **The relative square at finite scale** (`tendsto_relativeForm_add_relativeContact`). For two
  number fields `K`, `L`, the difference of the two pairings on the comb of the integers has the
  jets, the conjugate jets and the counterterm with the differences of the degrees, of the
  numbers of complex places and of the logarithms of the discriminants (`ringForm_sub`), and the
  contacts `(N_m^L(p) − N_m^K(p)) log p` (`relativeContact_prime_pow`). The pole planes cancel:
  it tends to `Z_K(f) − Z_L(f)`, minus the sum over the zeros of the quotient `ζ_L/ζ_K`. The
  integers have one point in every finite field (`fibrePointCount_rat`), so over `ℤ` the
  contacts of a number ring are `(N_m(p) − 1) log p` (`relativeContact_rat_prime_pow`).
-/

noncomputable section

open Finset Filter Topology NumberField
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens

/-! ### Homomorphisms into a finite field -/

section FiniteFields

/-- A finite field with `p^d` elements has characteristic `p`. -/
theorem charP_of_natCard_eq_prime_pow {E : Type*} [Field E] [Finite E] {p d : ℕ} (hp : p.Prime)
    (hE : Nat.card E = p ^ d) : CharP E p := by
  obtain ⟨q, hq⟩ := CharP.exists E
  haveI := hq
  haveI := Fintype.ofFinite E
  obtain ⟨n, hqp, hcard⟩ := FiniteField.card E q
  have hdvd : q ∣ p ^ d := by
    rw [← hE, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self q n.ne_zero
  have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow hdvd)
  exact hqe ▸ hq

/-- **Homomorphisms between finite fields.** A field with `p^d` elements maps to a field with
`p^m` elements only if `d ∣ m`, and then in exactly `d` ways. -/
theorem ringHom_finiteField {E F : Type*} [Field E] [Field F] [Finite E] [Finite F]
    {p d m : ℕ} (hp : p.Prime) (hE : Nat.card E = p ^ d) (hF : Nat.card F = p ^ m) :
    (Nonempty (E →+* F) → d ∣ m) ∧ Nat.card (E →+* F) = if d ∣ m then d else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charP_of_natCard_eq_prime_pow hp hE
  haveI := charP_of_natCard_eq_prime_pow hp hF
  letI : Algebra (ZMod p) E := ZMod.algebra E p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hdE : Module.finrank (ZMod p) E = d :=
    Nat.pow_right_injective hp.two_le ((FiniteField.pow_finrank_eq_natCard p E).trans hE)
  have hdF : Module.finrank (ZMod p) F = m :=
    Nat.pow_right_injective hp.two_le ((FiniteField.pow_finrank_eq_natCard p F).trans hF)
  -- a ring homomorphism is linear over the prime field
  let e : (E →+* F) ≃ (E →ₐ[ZMod p] F) :=
    { toFun := fun φ => { φ with
        commutes' := fun r => RingHom.congr_fun
          (Subsingleton.elim (φ.comp (algebraMap (ZMod p) E)) (algebraMap (ZMod p) F)) r }
      invFun := fun ψ => ψ.toRingHom
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  have hdvd : Nonempty (E →+* F) → d ∣ m := fun ⟨φ⟩ => by
    have h := FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨e φ⟩
    rwa [hdE, hdF] at h
  refine ⟨hdvd, ?_⟩
  by_cases h : d ∣ m
  · rw [if_pos h, Nat.card_congr e,
      FiniteField.natCard_algHom_of_finrank_dvd (by rw [hdE, hdF]; exact h), hdE]
  · rw [if_neg h]
    haveI : IsEmpty (E →+* F) := ⟨fun φ => h (hdvd ⟨φ⟩)⟩
    exact Nat.card_of_isEmpty

/-- A finite field that maps to a field with `p^m` elements has `p^d` elements with `d ∣ m`. -/
theorem exists_natCard_eq_of_ringHom_finiteField {E F : Type*} [Field E] [Field F] [Finite E]
    [Finite F] {p m : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ m) (ψ : E →+* F) :
    ∃ d, d ∣ m ∧ Nat.card E = p ^ d := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charP_of_natCard_eq_prime_pow hp hF
  haveI : CharP E p := ⟨fun x => by
    rw [← CharP.cast_eq_zero_iff F p x, ← map_natCast ψ x, map_eq_zero_iff ψ ψ.injective]⟩
  letI : Algebra (ZMod p) E := ZMod.algebra E p
  have hE := FiniteField.pow_finrank_eq_natCard p E
  exact ⟨_, (ringHom_finiteField hp hE.symm hF).1 ⟨ψ⟩, hE.symm⟩

/-- The ring homomorphisms into a field with a given maximal kernel are the ring homomorphisms
of the residue field. -/
def kerEquivQuotientHom {R F : Type*} [CommRing R] [Field F] (P : Ideal R) [P.IsMaximal] :
    {φ : R →+* F // RingHom.ker φ = P} ≃ (R ⧸ P →+* F) where
  toFun φ := Ideal.Quotient.lift P φ.1 fun a ha =>
    RingHom.mem_ker.mp (by rw [φ.2]; exact ha)
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mk P), by
    letI : Field (R ⧸ P) := Ideal.Quotient.field P
    ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff ψ ψ.injective,
      Ideal.Quotient.eq_zero_iff_mem]⟩
  left_inv φ := Subtype.ext (RingHom.ext fun a => rfl)
  right_inv ψ := Ideal.Quotient.ringHom_ext
    (Ideal.Quotient.lift_comp_mk P (ψ.comp (Ideal.Quotient.mk P)) _)

end FiniteFields

/-! ### Point counts -/

section PointCounts

variable (K : Type*) [Field K] [NumberField K]

/-- The prime ideals of norm `n`. -/
def primesOfNorm (n : ℕ) : Finset (Ideal (𝓞 K)) := (idealsOfNorm K n).filter fun P => P.IsPrime

variable {K} in
theorem mem_primesOfNorm {n : ℕ} {P : Ideal (𝓞 K)} :
    P ∈ primesOfNorm K n ↔ Ideal.absNorm P = n ∧ P.IsPrime := by
  rw [primesOfNorm, Finset.mem_filter, mem_idealsOfNorm]

/-- The number of points of the fibre of the ring of integers over `p` in the field with `p^m`
elements: a closed point of degree `d ∣ m` counts `d` times. -/
def fibrePointCount (p m : ℕ) : ℕ := ∑ d ∈ m.divisors, d * (primesOfNorm K (p ^ d)).card

variable {K} in
/-- A prime ideal power of norm `p^m` is a power of a prime ideal of norm `p^d`, `d k = m`. -/
theorem absNorm_eq_prime_pow_of_pow_eq {p m k : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hk : 1 ≤ k) (h : Ideal.absNorm P ^ k = p ^ m) :
    ∃ d, 1 ≤ d ∧ Ideal.absNorm P = p ^ d ∧ d * k = m := by
  have hdvd : Ideal.absNorm P ∣ p ^ m := h ▸ dvd_pow_self _ (by omega)
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd'
    · exact absurd (Ideal.absNorm_eq_one_iff.mp (by simpa using hd)) hP.ne_top
    · exact hd'
  refine ⟨d, hd1, hd, ?_⟩
  rw [hd, ← pow_mul] at h
  exact Nat.pow_right_injective hp.two_le h

/-- **The contacts at a prime power are the point count of the fibre.**
`Σ_{N𝔭^k = p^m} log N𝔭 = N_m(p) log p`. -/
theorem idealContact_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    idealContact K (p ^ m) = fibrePointCount K p m * Real.log p := by
  have hrhs : (fibrePointCount K p m : ℝ) * Real.log p =
      ∑ x ∈ m.divisors.sigma (fun d => primesOfNorm K (p ^ d)), (x.1 : ℝ) * Real.log p := by
    rw [Finset.sum_sigma, fibrePointCount]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hrhs, idealContact]
  symm
  refine Finset.sum_bij (fun x _ => (x.2, m / x.1)) ?_ ?_ ?_ ?_
  · -- a closed point of degree `d ∣ m` gives the power `m/d`
    rintro ⟨d, P⟩ hx
    obtain ⟨hd, hP⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hPn, hPp⟩ := mem_primesOfNorm.mp hP
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
    have hpow : Ideal.absNorm P ^ (m / d) = p ^ m := by
      rw [hPn, ← pow_mul, Nat.mul_div_cancel' hdm]
    rw [Finset.mem_filter, mem_primePowersLe]
    refine ⟨⟨hPp, ?_, Nat.div_pos (Nat.le_of_dvd hm hdm) hd0, hpow.le⟩, hpow⟩
    rintro rfl
    rw [Ideal.absNorm_bot] at hPn
    exact (pow_pos hp.pos d).ne hPn
  · rintro ⟨d, P⟩ hx ⟨d', P'⟩ hx' h
    have hPn := (mem_primesOfNorm.mp (Finset.mem_sigma.mp hx).2).1
    have hPn' := (mem_primesOfNorm.mp (Finset.mem_sigma.mp hx').2).1
    obtain rfl : P = P' := (Prod.mk.inj h).1
    obtain rfl : d = d' := Nat.pow_right_injective hp.two_le (hPn.symm.trans hPn')
    rfl
  · rintro ⟨P, k⟩ hPk
    obtain ⟨hmem, hpow⟩ := Finset.mem_filter.mp hPk
    obtain ⟨hPp, -, hk, -⟩ := mem_primePowersLe.mp hmem
    obtain ⟨d, hd1, hd, hdk⟩ := absNorm_eq_prime_pow_of_pow_eq hp hPp hk hpow
    refine ⟨⟨d, P⟩, Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨⟨k, hdk.symm⟩, by omega⟩,
      mem_primesOfNorm.mpr ⟨hd, hPp⟩⟩, ?_⟩
    show (P, m / d) = (P, k)
    rw [← hdk, Nat.mul_div_cancel_left k hd1]
  · rintro ⟨d, P⟩ hx
    have hPn := (mem_primesOfNorm.mp (Finset.mem_sigma.mp hx).2).1
    show (d : ℝ) * Real.log p = Real.log ((Ideal.absNorm P : ℕ) : ℝ)
    rw [hPn, Nat.cast_pow, Real.log_pow]

/-- **A norm that is not a prime power carries no contact.** -/
theorem idealContact_eq_zero {n : ℕ} (hn : ¬ IsPrimePow n) : idealContact K n = 0 := by
  rw [idealContact]
  refine Finset.sum_eq_zero fun pk hpk => absurd ?_ hn
  obtain ⟨P, k⟩ := pk
  obtain ⟨hmem, hpow⟩ := Finset.mem_filter.mp hpk
  obtain ⟨hP, hP0, hk, -⟩ := mem_primePowersLe.mp hmem
  haveI := hP.isMaximal hP0
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, -, f, hq, hcard⟩ := FiniteField.card' (𝓞 K ⧸ P)
  have hN : Ideal.absNorm P = q ^ (f : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  rw [← hpow, hN, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨q, (f : ℕ) * k, hq, Nat.mul_pos f.pos (by omega), rfl⟩

/-! ### The points of the fibre -/

variable {F : Type*} [Field F] [Finite F]

/-- The homomorphisms into a field with `p^m` elements whose kernel is a given prime ideal of
norm `p^d`: `d` of them if `d ∣ m`, none otherwise. -/
theorem natCard_ringHom_ker_eq {p d m : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ m)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOfNorm K (p ^ d)) :
    Nat.card {φ : 𝓞 K →+* F // RingHom.ker φ = P} = if d ∣ m then d else 0 := by
  obtain ⟨hPn, hPp⟩ := mem_primesOfNorm.mp hP
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hPn
    exact (pow_pos hp.pos d).ne hPn
  haveI := hPp.isMaximal hP0
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hE : Nat.card (𝓞 K ⧸ P) = p ^ d := by
    rw [← hPn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (kerEquivQuotientHom P), (ringHom_finiteField hp hE hF).2]

/-- The kernel of a homomorphism into a field with `p^m` elements is a prime ideal of norm
`p^d` with `d ∣ m`. -/
theorem ker_mem_biUnion_primesOfNorm {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hF : Nat.card F = p ^ m) (φ : 𝓞 K →+* F) :
    RingHom.ker φ ∈ m.divisors.biUnion fun d => primesOfNorm K (p ^ d) := by
  haveI := charP_of_natCard_eq_prime_pow hp hF
  have hprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hp0 : RingHom.ker φ ≠ ⊥ := by
    intro h0
    have hmem : (p : 𝓞 K) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h0, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  haveI := hprime.isMaximal hp0
  letI : Field (𝓞 K ⧸ RingHom.ker φ) := Ideal.Quotient.field _
  -- the residue field embeds into `F`
  obtain ⟨d, hdvd, hE⟩ := exists_natCard_eq_of_ringHom_finiteField hp hF (RingHom.kerLift φ)
  refine Finset.mem_biUnion.mpr ⟨d, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩,
    mem_primesOfNorm.mpr ⟨?_, hprime⟩⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hE]

/-- **The point count of the fibre.** `N_m(p) = Σ_{d ∣ m} d a_d(p)` is the number of ring
homomorphisms from the ring of integers into a field with `p^m` elements: the homomorphisms
with kernel `𝔭` are the embeddings of the residue field of `𝔭`. -/
theorem natCard_ringHom_eq_fibrePointCount {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hF : Nat.card F = p ^ m) : Nat.card (𝓞 K →+* F) = fibrePointCount K p m := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Ideal (𝓞 K)),
      T = m.divisors.biUnion fun d => primesOfNorm K (p ^ d) := ⟨_, rfl⟩
  have hker : ∀ φ : 𝓞 K →+* F, RingHom.ker φ ∈ T := fun φ => by
    rw [hT]
    exact ker_mem_biUnion_primesOfNorm K hp hm hF φ
  have hcard : ∀ d ∈ m.divisors, ∀ P ∈ primesOfNorm K (p ^ d),
      Nat.card {φ : 𝓞 K →+* F // RingHom.ker φ = P} = d := fun d hd P hP => by
    rw [natCard_ringHom_ker_eq K hp hF hP, if_pos (Nat.dvd_of_mem_divisors hd)]
  have hmemT : ∀ P ∈ T, ∃ d ∈ m.divisors, P ∈ primesOfNorm K (p ^ d) := fun P hP => by
    rw [hT] at hP
    exact Finset.mem_biUnion.mp hP
  -- a homomorphism is its kernel and itself
  let f : (𝓞 K →+* F) → T := fun φ => ⟨RingHom.ker φ, hker φ⟩
  have hfib : ∀ P : T, Nat.card {φ : 𝓞 K →+* F // f φ = P} =
      Nat.card {φ : 𝓞 K →+* F // RingHom.ker φ = (P : Ideal (𝓞 K))} := fun P =>
    Nat.card_congr (Equiv.subtypeEquivRight fun φ => Subtype.ext_iff)
  haveI : ∀ P : T, Finite {φ : 𝓞 K →+* F // f φ = P} := fun P => by
    obtain ⟨d, hd, hP⟩ := hmemT P P.2
    refine Nat.finite_of_card_ne_zero ?_
    rw [hfib P, hcard d hd _ hP]
    exact (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hm).ne'
  have hdisj : (m.divisors : Set ℕ).PairwiseDisjoint fun d => primesOfNorm K (p ^ d) :=
    fun d _ d' _ hne => Finset.disjoint_left.mpr fun P h h' =>
      hne (Nat.pow_right_injective hp.two_le
        ((mem_primesOfNorm.mp h).1.symm.trans (mem_primesOfNorm.mp h').1))
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma, Fintype.sum_congr _ _ hfib,
    Finset.sum_coe_sort T (fun P => Nat.card {φ : 𝓞 K →+* F // RingHom.ker φ = P}), hT,
    Finset.sum_biUnion hdisj, fibrePointCount]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_congr rfl (hcard d hd), Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The contacts of a number ring are its point counts.** The contact order of the norm `p^m`
is `log p` times the number of points of the ring of integers in a field with `p^m` elements. -/
theorem idealContact_prime_pow_eq_natCard_ringHom {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hF : Nat.card F = p ^ m) :
    idealContact K (p ^ m) = (Nat.card (𝓞 K →+* F) : ℝ) * Real.log p := by
  rw [idealContact_prime_pow K hp hm, natCard_ringHom_eq_fibrePointCount K hp hm hF]

/-- **The integers have one point in every finite field**: `N_m(p) = 1` for `ℤ`. -/
theorem fibrePointCount_rat {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    fibrePointCount ℚ p m = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  rw [← natCard_ringHom_eq_fibrePointCount ℚ hp hm hF]
  haveI : Nonempty (𝓞 ℚ →+* GaloisField p m) :=
    ⟨(Int.castRingHom (GaloisField p m)).comp Rat.ringOfIntegersEquiv.toRingHom⟩
  haveI : Subsingleton (𝓞 ℚ →+* GaloisField p m) := ⟨fun φ ψ => RingHom.ext fun x => by
    have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) := by
      rw [← map_intCast Rat.ringOfIntegersEquiv.symm, RingEquiv.symm_apply_apply]
    rw [hx, map_intCast, map_intCast]⟩
  exact Nat.card_unique

end PointCounts

/-! ### The relative square at finite scale -/

section Relative

/-- The contacts are linear in the weight. -/
theorem weightedContact_sub (w v : ℕ → ℝ) (f : ℝ → ℝ) (L₀ N : ℕ) :
    weightedContact (fun n => w n - v n) f L₀ N =
      weightedContact w f L₀ N - weightedContact v f L₀ N := by
  simp only [weightedContact, sub_div, sub_mul, Finset.sum_sub_distrib]

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]

/-- The jets and the counterterm of the relative square: the differences of the degrees, of the
numbers of complex places and of the logarithms of the discriminants. -/
theorem ringForm_sub (f : ℝ → ℝ) (L₀ N : ℕ) :
    ringForm L f L₀ N - ringForm K f L₀ N =
      ((placeDegree L : ℝ) - placeDegree K) * degreeForm f L₀ N -
        ((InfinitePlace.nrComplexPlaces L : ℝ) - InfinitePlace.nrComplexPlaces K) *
          conjugateJet f L₀ N -
        (Real.log |(NumberField.discr L : ℝ)| - Real.log |(NumberField.discr K : ℝ)|) *
          ∑ n ∈ Ioc N (N + L₀ * N), degreeSample f N n ^ 2 / n := by
  rw [ringForm, ringForm]
  ring

/-- **The contacts of the relative square are differences of point counts.** -/
theorem relativeContact_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    idealContact L (p ^ m) - idealContact K (p ^ m) =
      ((fibrePointCount L p m : ℝ) - fibrePointCount K p m) * Real.log p := by
  rw [idealContact_prime_pow L hp hm, idealContact_prime_pow K hp hm]
  ring

/-- **The contacts of a number ring over the integers** are `(N_m(p) − 1) log p`, with `N_m(p)`
the number of points of the ring in a field with `p^m` elements. -/
theorem relativeContact_rat_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) {F : Type*}
    [Field F] [Finite F] (hF : Nat.card F = p ^ m) :
    idealContact K (p ^ m) - idealContact ℚ (p ^ m) =
      ((Nat.card (𝓞 K →+* F) : ℝ) - 1) * Real.log p := by
  rw [relativeContact_prime_pow ℚ K hp hm, fibrePointCount_rat hp hm,
    natCard_ringHom_eq_fibrePointCount K hp hm hF, Nat.cast_one]

/-- **The relative square of two number rings at finite scale.** The difference of the pairings
of the ideals of `L` and of `K`, with the contacts `(N_m^L(p) − N_m^K(p)) log p`, has no pole
plane: it tends to `Z_K(f) − Z_L(f)`. -/
theorem tendsto_relativeForm_add_relativeContact {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K₀ : ℕ} (hK : 1 ≤ K₀)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ringForm L f (3 * K₀) N - ringForm K f (3 * K₀) N +
        2 * weightedContact (fun n => idealContact L n - idealContact K n) f (3 * K₀) N) atTop
      (𝓝 (dedekindZeroSum K f - dedekindZeroSum L f)) := by
  have h := (tendsto_ringForm_add_idealContact L hf hfc hK hsupp).sub
    (tendsto_ringForm_add_idealContact K hf hfc hK hsupp)
  convert h using 1
  · funext N
    rw [weightedContact_sub]
    ring
  · congr 1
    ring

end Relative

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
