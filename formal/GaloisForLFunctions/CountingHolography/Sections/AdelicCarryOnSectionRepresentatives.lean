import GaloisForLFunctions.CountingHolography.Sections.ReversibleCarryOnMixedSectionFamilies
import GaloisForLFunctions.CountingHolography.Sections.TwoOutputCarryPrecisionObstructions
import GaloisForLFunctions.CountingHolography.Sections.EffectiveSectionsAtSeparatedConductors

/-!
# Adelic ternary carry on rational section representatives

Each integer small-section coordinate `z ∈ divisorSections v` indexes the actual
rational section representative `sectionRep v z = generator v * z ∈ ℚ` in the
fractional ideal `d(v) ℤ` cut out by all finite-place prime contact valuations
and bounded at infinity by `exp (radius v)`.

1. **Midpoint-only and finite-place-only obstructions:** Because `(2m)(kb) = m(2kb)`
   has identical rational section representatives, no map `Φ : ℚ × ℚ → ℚ × ℚ`
   ignoring the outer target lattices can serve distinct translations with
   subquadratic fibre loss when `Q(b + a) ≠ Q(b - a)`. On `primePair p`, both the
   archimedean radius rate and the finite-place log-generator rate grow at least as
   fast as `c₀ √p`, while their difference `Q(primePair p)` is `o(√p)`; hence any
   carry schedule driven by finite-place generator ratios alone overshoots the
   carry window `(5 Q(b_p), 7 Q(b_p))` at every large prime `p`.
2. **One explicit adelic ternary carry rule and valuation-paid decoder:** The outer
   Arakelov skew `outerAdelicSkew v₁ v₂ = ((radius v₁ - log d(v₁)) - (radius v₂ - log d(v₂))) / 2`
   depends neither on the midpoint `v₀` nor on any section cardinality. Setting
   `τ = ⌊|outerAdelicSkew v₁ v₂| / log 3⌋₊` and `K = (3^τ - 1) / 2` (`2K + 1 = 3^τ`),
   `adelicSectionEncode` and `adelicSectionDecode` establish an exact bijection
   between `(d(v₀) ℤ)²` and `d(v₁) ℤ × d(v₂) ℤ` for all triples `(v₀, v₁, v₂)`.
   The `3^τ` ambiguous narrow-slice candidates are uniquely paid by the `3`-adic
   valuation of the wide rational section difference (`ratPrimeVal 3`); once paid,
   every coprime modulus `u` (`gcd(u, 3) = 1`) recovers `(z₁ mod u, z₂ mod u)` with
   zero precision loss, and asymmetric `3`-adic recovery uses `(r + τ) + (r - τ) = 2r`
   total ternary digits.
3. **Asymptotic validity and single-rule RH equivalence:** Whenever `v₁ = v₂ = v₀`
   or `0 < Q(v₀), Q(v₁), Q(v₂)` with `2 Q(v₀) < Q(v₁) + Q(v₂)`, `adelicSectionEncode`
   maps `rationalSections (m • v₀)²` injectively (`maxFibre = 1`) into
   `rationalSections (m • v₁) × rationalSections (m • v₂)` for all large `m`. Over
   the fixed two-atom prime background `b`, RH is equivalent to this single rule
   succeeding across all displacements.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography

/-! ### 1. Rational section representatives and signed prime valuations -/

/-- Rational section representative `d(v) · z ∈ ℚ` of an integer lattice coordinate `z`. -/
def sectionRep {N : ℕ} (v : Fin N → ℤ) (z : ℤ) : ℚ :=
  generator v * z

/-- Recover the integer lattice coordinate from a rational section representative in `d(v) ℤ`. -/
def sectionCoord {N : ℕ} (v : Fin N → ℤ) (s : ℚ) : ℤ :=
  (s / generator v).num

/-- Membership in the fractional ideal `d(v) ℤ ⊂ ℚ` cut out by all finite-place valuations. -/
def inSectionLattice {N : ℕ} (v : Fin N → ℤ) (s : ℚ) : Prop :=
  (s / generator v).den = 1

theorem generator_pos_rat {N : ℕ} (v : Fin N → ℤ) : 0 < generator v :=
  contactGenerator_pos _ _ _

theorem sectionRep_injective {N : ℕ} (v : Fin N → ℤ) : Function.Injective (sectionRep v) := by
  intro z₁ z₂ h
  exact Int.cast_injective (mul_left_cancel₀ (generator_pos_rat v).ne' h)

theorem sectionCoord_sectionRep {N : ℕ} (v : Fin N → ℤ) (z : ℤ) :
    sectionCoord v (sectionRep v z) = z := by
  unfold sectionCoord sectionRep
  rw [mul_div_cancel_left₀ _ (generator_pos_rat v).ne']
  exact Rat.num_intCast z

theorem inSectionLattice_sectionRep {N : ℕ} (v : Fin N → ℤ) (z : ℤ) :
    inSectionLattice v (sectionRep v z) := by
  unfold inSectionLattice sectionRep
  rw [mul_div_cancel_left₀ _ (generator_pos_rat v).ne']
  exact Rat.den_intCast z

theorem sectionRep_sectionCoord {N : ℕ} {v : Fin N → ℤ} {s : ℚ} (hs : inSectionLattice v s) :
    sectionRep v (sectionCoord v s) = s := by
  unfold sectionRep sectionCoord
  let q : ℚ := s / generator v
  have hden : q.den = 1 := hs
  have hq : (q.num : ℚ) = q := by
    have hd := Rat.num_div_den q
    rw [hden, Nat.cast_one, div_one] at hd
    exact hd
  change generator v * (q.num : ℚ) = s
  rw [hq]
  exact mul_div_cancel₀ s (generator_pos_rat v).ne'

theorem inSectionLattice_iff_exists_int {N : ℕ} (v : Fin N → ℤ) (s : ℚ) :
    inSectionLattice v s ↔ ∃ z : ℤ, s = sectionRep v z := by
  constructor
  · exact fun hs => ⟨sectionCoord v s, (sectionRep_sectionCoord hs).symm⟩
  · rintro ⟨z, rfl⟩
    exact inSectionLattice_sectionRep v z

/-- Signed `ℤ`-valued prime valuation on nonzero rationals. -/
def ratPrimeVal (p : ℕ) (r : ℚ) : ℤ :=
  (r.num.natAbs.factorization p : ℤ) - (r.den.factorization p : ℤ)

theorem ratPrimeVal_mul {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (p : ℕ) :
    ratPrimeVal p (x * y) = ratPrimeVal p x + ratPrimeVal p y := by
  let q := x * y
  have hq : q ≠ 0 := mul_ne_zero hx hy
  have hxn : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hyn : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hy)
  have hqn : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hxd : x.den ≠ 0 := x.den_ne_zero
  have hyd : y.den ≠ 0 := y.den_ne_zero
  have hqd : q.den ≠ 0 := q.den_ne_zero
  have hrat : ((q.num : ℚ) / q.den) = ((x.num : ℚ) / x.den) * ((y.num : ℚ) / y.den) := by
    rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  have hcross_q : (q.num : ℚ) * (x.den * y.den) = (x.num * y.num) * q.den := by
    have h1 := hrat
    field_simp [Nat.cast_ne_zero.mpr hqd, Nat.cast_ne_zero.mpr hxd, Nat.cast_ne_zero.mpr hyd] at h1
    linarith only [h1]
  have hcross_z : q.num * ((x.den * y.den : ℕ) : ℤ) = (x.num * y.num) * (q.den : ℤ) := by
    exact_mod_cast hcross_q
  have hcross_n : q.num.natAbs * (x.den * y.den) = (x.num.natAbs * y.num.natAbs) * q.den := by
    have habs := congrArg Int.natAbs hcross_z
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using habs
  have hf := congrArg (fun n : ℕ => (n.factorization p : ℤ)) hcross_n
  rw [Nat.factorization_mul hqn (Nat.mul_ne_zero hxd hyd),
    Nat.factorization_mul hxd hyd,
    Nat.factorization_mul (Nat.mul_ne_zero hxn hyn) hqd,
    Nat.factorization_mul hxn hyn] at hf
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add] at hf
  dsimp only [ratPrimeVal, q] at hf ⊢
  linarith only [hf]

/-- Nonzero rational section-lattice membership is equivalent to dominating `generator v`
at every prime valuation. -/
theorem inSectionLattice_iff_primeValuations {N : ℕ} (v : Fin N → ℤ) {s : ℚ} (hs : s ≠ 0) :
    inSectionLattice v s ↔ ∀ p : ℕ, p.Prime → ratPrimeVal p (generator v) ≤ ratPrimeVal p s := by
  let d := generator v
  have hd : d ≠ 0 := (generator_pos_rat v).ne'
  let q := s / d
  have hq : q ≠ 0 := div_ne_zero hs hd
  have hsd : s = d * q := (mul_div_cancel₀ s hd).symm
  constructor
  · intro hden p _
    rw [hsd, ratPrimeVal_mul hd hq p]
    have hd1 : q.den = 1 := hden
    have hq_nonneg : 0 ≤ ratPrimeVal p q := by
      unfold ratPrimeVal
      rw [hd1, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, sub_zero]
      exact Nat.cast_nonneg _
    linarith only [hq_nonneg]
  · intro hall
    unfold inSectionLattice
    change q.den = 1
    by_contra hne
    let p := q.den.minFac
    have hp : p.Prime := Nat.minFac_prime hne
    have hp_dvd : p ∣ q.den := Nat.minFac_dvd q.den
    have hnot_num : ¬ (p ∣ q.num.natAbs) := by
      intro hdiv
      exact hp.not_dvd_one (q.reduced.gcd_eq_one ▸ Nat.dvd_gcd hdiv hp_dvd)
    have hf_num : q.num.natAbs.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot_num
    have hf_den : 0 < q.den.factorization p :=
      hp.factorization_pos_of_dvd q.den_pos.ne' hp_dvd
    have hv := hall p hp
    rw [hsd, ratPrimeVal_mul hd hq p] at hv
    dsimp only [d] at hv
    unfold ratPrimeVal at hv
    rw [hf_num] at hv
    have hf_pos : (0 : ℤ) < q.den.factorization p := by exact_mod_cast hf_den
    linarith only [hv, hf_pos]

/-- For any prime `p`, positive rational generator `d > 0`, integer `z`, and order `r`,
`p^r ∣ z` in `ℤ` iff either `d * z = 0` or `ratPrimeVal p d + r ≤ ratPrimeVal p (d * z)`. -/
theorem pow_dvd_int_iff_ratPrimeVal {p r : ℕ} (hp : p.Prime) {d : ℚ} (hd : 0 < d) (z : ℤ) :
    ((p : ℤ) ^ r ∣ z) ↔
      (d * (z : ℚ) = 0 ∨ ratPrimeVal p d + (r : ℤ) ≤ ratPrimeVal p (d * (z : ℚ))) := by
  by_cases hz : z = 0
  · subst z; simp
  · have hzc : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hz
    have hdz : d * (z : ℚ) ≠ 0 := mul_ne_zero hd.ne' hzc
    have hval_z : ratPrimeVal p (z : ℚ) = (z.natAbs.factorization p : ℤ) := by
      unfold ratPrimeVal
      rw [Rat.num_intCast, Rat.den_intCast, Nat.factorization_one,
        Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, sub_zero]
    have hdvd_abs : ((p : ℤ) ^ r ∣ z) ↔ p ^ r ∣ z.natAbs := by
      constructor
      · rintro ⟨k, hk⟩
        rw [← Nat.cast_pow p r] at hk
        refine ⟨k.natAbs, ?_⟩
        have habs := congrArg Int.natAbs hk
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using habs
      · rintro ⟨k, hk⟩
        rcases Int.natAbs_eq z with h | h
        · rw [h, hk]; push_cast; exact dvd_mul_right _ _
        · rw [h, hk]; push_cast; exact (dvd_mul_right _ _).neg_right
    rw [hdvd_abs, hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hz),
      or_iff_right hdz, ratPrimeVal_mul hd.ne' hzc p, hval_z]
    omega

/-- Finite set of actual rational small-section representatives of `v`. -/
def rationalSections {N : ℕ} (v : Fin N → ℤ) : Finset ℚ :=
  (divisorSections v).map ⟨sectionRep v, sectionRep_injective v⟩

theorem card_rationalSections {N : ℕ} (v : Fin N → ℤ) :
    (rationalSections v).card = (divisorSections v).card :=
  Finset.card_map _

/-- A rational number is a small section representative of `v` iff it lies in `d(v) ℤ`
and satisfies the archimedean bound `|s| ≤ exp(radius v)`. -/
theorem mem_rationalSections_iff {N : ℕ} (v : Fin N → ℤ) (s : ℚ) :
    s ∈ rationalSections v ↔ inSectionLattice v s ∧ |(s : ℝ)| ≤ Real.exp (radius v) := by
  have hd : 0 < (generator v : ℝ) := by exact_mod_cast generator_pos_rat v
  rw [rationalSections, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    dsimp only [Function.Embedding.coeFn_mk]
    refine ⟨inSectionLattice_sectionRep v z, ?_⟩
    have hm := (mem_smallSections hd z).mp hz
    simpa only [sectionRep, Rat.cast_mul, Rat.cast_intCast] using hm
  · rintro ⟨hs, habs⟩
    refine ⟨sectionCoord v s, ?_, sectionRep_sectionCoord hs⟩
    apply (mem_smallSections hd _).mpr
    have heq : ((generator v : ℝ) * (sectionCoord v s : ℝ)) = (s : ℝ) := by
      have h := congrArg (fun r : ℚ => (r : ℝ)) (sectionRep_sectionCoord hs)
      simpa only [sectionRep, Rat.cast_mul, Rat.cast_intCast] using h
    rwa [heq]

/-- Canonical equivalence between integer small-section coordinates and rational section representatives. -/
def rationalSectionEquiv {N : ℕ} (v : Fin N → ℤ) :
    ↥(divisorSections v) ≃ ↥(rationalSections v) where
  toFun z := ⟨sectionRep v z.val, Finset.mem_map.mpr ⟨z.val, z.property, rfl⟩⟩
  invFun s := ⟨sectionCoord v s.val, by
    obtain ⟨z, hz, hzs⟩ := Finset.mem_map.mp s.property
    dsimp only [Function.Embedding.coeFn_mk] at hzs
    rw [← hzs, sectionCoord_sectionRep]
    exact hz⟩
  left_inv z := Subtype.ext (sectionCoord_sectionRep v z.val)
  right_inv s := Subtype.ext (by
    obtain ⟨z, _, hzs⟩ := Finset.mem_map.mp s.property
    dsimp only [Function.Embedding.coeFn_mk] at hzs
    exact sectionRep_sectionCoord (hzs ▸ inSectionLattice_sectionRep v z))

/-! ### 2. Midpoint-only section-representative rigidity and finite-place skew divergence -/

/-- A map on pairs of rational section representatives sends `rationalSections v₀²`
into `rationalSections v₁ × rationalSections v₂`. -/
def mapsRationalSections {N : ℕ} (Φ : ℚ × ℚ → ℚ × ℚ) (v₀ v₁ v₂ : Fin N → ℤ) : Prop :=
  ∀ s₁ ∈ rationalSections v₀, ∀ s₂ ∈ rationalSections v₀,
    (Φ (s₁, s₂)).1 ∈ rationalSections v₁ ∧ (Φ (s₁, s₂)).2 ∈ rationalSections v₂

/-- Restriction of a rational-section map `Φ` to the finite rational section sets. -/
def restrictRationalSectionMap {N : ℕ} (Φ : ℚ × ℚ → ℚ × ℚ) {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsRationalSections Φ v₀ v₁ v₂) :
    (↥(rationalSections v₀) × ↥(rationalSections v₀)) →
      (↥(rationalSections v₁) × ↥(rationalSections v₂)) :=
  fun p => (⟨(Φ (p.1.val, p.2.val)).1, (h p.1.val p.1.property p.2.val p.2.property).1⟩,
            ⟨(Φ (p.1.val, p.2.val)).2, (h p.1.val p.1.property p.2.val p.2.property).2⟩)

/-- Induced map on integer small-section coordinates via `rationalSectionEquiv`. -/
def inducedDivisorSectionMap {N : ℕ} {Φ : ℚ × ℚ → ℚ × ℚ} {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsRationalSections Φ v₀ v₁ v₂) :
    (↥(divisorSections v₀) × ↥(divisorSections v₀)) →
      (↥(divisorSections v₁) × ↥(divisorSections v₂)) :=
  fun p => ((rationalSectionEquiv v₁).symm.prodCongr (rationalSectionEquiv v₂).symm)
    (restrictRationalSectionMap Φ h
      (((rationalSectionEquiv v₀).prodCongr (rationalSectionEquiv v₀)) p))

theorem maxFibre_inducedDivisorSectionMap {N : ℕ} {Φ : ℚ × ℚ → ℚ × ℚ} {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsRationalSections Φ v₀ v₁ v₂) :
    maxFibre (inducedDivisorSectionMap h) = maxFibre (restrictRationalSectionMap Φ h) :=
  maxFibre_comp_equiv ((rationalSectionEquiv v₀).prodCongr (rationalSectionEquiv v₀))
    ((rationalSectionEquiv v₁).symm.prodCongr (rationalSectionEquiv v₂).symm)
    (restrictRationalSectionMap Φ h)

theorem maxFibre_restrictRationalSectionMap_eq {N : ℕ} (Φ : ℚ × ℚ → ℚ × ℚ)
    {v₀ v₁ v₂ w₁ w₂ : Fin N → ℤ}
    (h₁ : mapsRationalSections Φ v₀ v₁ v₂) (h₂ : mapsRationalSections Φ v₀ w₁ w₂) :
    maxFibre (restrictRationalSectionMap Φ h₁) = maxFibre (restrictRationalSectionMap Φ h₂) := by
  have hle : ∀ {a₁ a₂ b₁ b₂ : Fin N → ℤ}
      (u₁ : mapsRationalSections Φ v₀ a₁ a₂) (u₂ : mapsRationalSections Φ v₀ b₁ b₂),
      maxFibre (restrictRationalSectionMap Φ u₁) ≤ maxFibre (restrictRationalSectionMap Φ u₂) := by
    intro a₁ a₂ b₁ b₂ u₁ u₂
    rw [maxFibre_le_iff]
    intro y S hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · simp
    · refine card_le_maxFibre_of_forall_eq (restrictRationalSectionMap Φ u₂)
        (restrictRationalSectionMap Φ u₂ p) fun q hq => ?_
      have heq : restrictRationalSectionMap Φ u₁ q = restrictRationalSectionMap Φ u₁ p :=
        (hS q hq).trans (hS p hp).symm
      simp only [restrictRationalSectionMap, Prod.ext_iff, Subtype.ext_iff] at heq ⊢
      exact heq
  exact le_antisymm (hle h₁ h₂) (hle h₂ h₁)

private theorem rational_card_sq_le_of_two_targets {N : ℕ} (Φ : ℚ × ℚ → ℚ × ℚ)
    {v₀ v₁ v₂ w₁ w₂ : Fin N → ℤ}
    (h₁ : mapsRationalSections Φ v₀ v₁ v₂) (h₂ : mapsRationalSections Φ v₀ w₁ w₂) :
    (divisorSections v₀).card ^ 2 ≤
      maxFibre (restrictRationalSectionMap Φ h₁) *
        ((divisorSections w₁).card * (divisorSections v₂).card) := by
  have hint : mapsRationalSections Φ v₀ w₁ v₂ := fun x hx y hy =>
    ⟨(h₂ x hx y hy).1, (h₁ x hx y hy).2⟩
  rw [maxFibre_restrictRationalSectionMap_eq Φ h₁ hint]
  have hc := card_le_maxFibre_mul_card (restrictRationalSectionMap Φ hint)
  simpa only [Fintype.card_prod, Fintype.card_coe, card_rationalSections, sq] using hc

/-- No single map `Φ : ℚ × ℚ → ℚ × ℚ` depending only on the midpoint rational section
representatives (ignoring the outer target lattices) can serve all sufficiently high
background translations with subquadratic logarithmic fibres when `Q(b + a) ≠ Q(b - a)`. -/
theorem not_exists_midpointOnly_subquadratic_rationalSectionMap {N : ℕ} {b a : Fin N → ℤ}
    (hb : 0 < integerProbe N b) (hmix : integerProbe N (b + a) ≠ integerProbe N (b - a)) :
    ¬ ∃ Φ : ℚ × ℚ → ℚ × ℚ, ∀ᶠ k : ℕ in atTop,
      (∀ᶠ m : ℕ in atTop,
        mapsRationalSections Φ (m • (k • b)) (m • (k • b + a)) (m • (k • b - a))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ᶠ m : ℕ in atTop,
        ∃ h : mapsRationalSections Φ (m • (k • b)) (m • (k • b + a)) (m • (k • b - a)),
          Real.log (maxFibre (restrictRationalSectionMap Φ h)) ≤ ε * (m : ℝ)^2 := by
  rintro ⟨Φ, hΦ⟩
  have hshift_diff (r s : ℕ) :
      integerProbe N (r • b + s • a) - integerProbe N (r • b - s • a) =
        (r : ℝ) * (s : ℝ) * (integerProbe N (b + a) - integerProbe N (b - a)) := by
    have hsmul {m : ℕ} (v : Fin N → ℤ) (i : Fin N) : ((m • v) i : ℝ) = (m : ℝ) * (v i : ℝ) := by
      change ((m • v i : ℤ) : ℝ) = _
      rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    simp only [integerProbe_eq_sum, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub, hsmul]
    simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    ((hΦ.and (eventually_positive_shift b a hb)).and
      ((eventually_positive_shift b (-a) hb).and
        ((eventually_positive_shift b (2 • a) hb).and (eventually_positive_shift b (-(2 • a)) hb))))
  let Δ := |integerProbe N (b + a) - integerProbe N (b - a)|
  have hΔ : 0 < Δ := abs_pos.mpr (sub_ne_zero.mpr hmix)
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt ((5 * |integerProbe N a| + 4) / Δ)
  let k := max (max K₀ 1) K₁
  have hk0 : K₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have h2k0 : K₀ ≤ 2 * k := by omega
  have hgap_k : 5 * integerProbe N a + 4 < (k : ℝ) * Δ := by
    have hkK₁ : (K₁ : ℝ) ≤ k := by exact_mod_cast le_max_right (max K₀ 1) K₁
    have hgt := (div_lt_iff₀ hΔ).mp (hK₁.trans_le hkK₁)
    linarith only [hgt, le_abs_self (integerProbe N a)]
  obtain ⟨⟨⟨hm_k, _⟩, _⟩, _, _⟩ := hK₀ k hk0
  obtain ⟨⟨⟨_, hfib_2k⟩, hp_2k_a⟩, hn_2k_a, hp_2k_2a, hn_2k_2a⟩ := hK₀ (2 * k) h2k0
  rw [← sub_eq_add_neg] at hn_2k_a hn_2k_2a
  have hmid_pos : 0 ≤ integerProbe N ((2 * k) • b) := by
    rw [integerProbe_smul]; exact mul_nonneg (sq_nonneg _) hb.le
  have hp1 := integerProbe_parallelogram N ((2 * k) • b) a
  have hp2 := integerProbe_parallelogram N ((2 * k) • b) (2 • a)
  rw [integerProbe_smul N 2 a] at hp2
  have hp3 := hshift_diff (2 * k) 1
  simp only [one_smul, Nat.cast_one, mul_one, Nat.cast_mul, Nat.cast_ofNat] at hp3
  have hp4 := hshift_diff (2 * k) 2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp4
  push_cast at hp2
  have h2m_map : ∀ᶠ m : ℕ in atTop,
      mapsRationalSections Φ ((2 * m) • (k • b)) ((2 * m) • (k • b + a)) ((2 * m) • (k • b - a)) := by
    have ht : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_atTop_mono (f := id) (fun m => by dsimp; omega) tendsto_id
    exact ht.eventually hm_k
  have hc_pos_real (v : Fin N → ℤ) : 0 < ((divisorSections v).card : ℝ) := by
    have : 0 < (divisorSections v).card := by rw [divisorSections, card_smallSections]; omega
    exact_mod_cast this
  have hnonempty (v : Fin N → ℤ) : Nonempty ↥(rationalSections v) := by
    have hc : 0 < (rationalSections v).card := by
      rw [card_rationalSections, divisorSections, card_smallSections]; omega
    exact Finset.Nonempty.to_subtype (Finset.card_pos.mp hc)
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hmix) with hneg_mix | hpos_mix
  · have hΔ_eq : Δ = -(integerProbe N (b + a) - integerProbe N (b - a)) := abs_of_neg hneg_mix
    have hdef : 4 < 2 * integerProbe N ((2 * k) • b) -
        integerProbe N ((2 * k) • b + 2 • a) - integerProbe N ((2 * k) • b - a) := by
      rw [hΔ_eq] at hgap_k; linarith only [hp1, hp2, hp3, hp4, hgap_k]
    have hl₀ := logCard_tateLimit ((2 * k) • b); rw [max_eq_left hmid_pos] at hl₀
    have hl₁ := logCard_tateLimit ((2 * k) • b + 2 • a); rw [max_eq_left hp_2k_2a.le] at hl₁
    have hl₂ := logCard_tateLimit ((2 * k) • b - a); rw [max_eq_left hn_2k_a.le] at hl₂
    have hlim := ((hl₀.const_mul 2).sub hl₁).sub hl₂
    obtain ⟨m, ⟨h_2k, hsmall⟩, h_k2m, h_rate, hm1⟩ :=
      ((hfib_2k 1 one_pos).and_eventually
        (h2m_map.and ((hlim.eventually_const_lt hdef).and (eventually_ge_atTop 1)))).exists
    have he₀ : (2 * m) • (k • b) = m • ((2 * k) • b) := by
      rw [smul_smul, smul_smul, show 2 * m * k = m * (2 * k) by ring]
    have he₁ : (2 * m) • (k • b + a) = m • ((2 * k) • b + 2 • a) := by
      ext i; change (2 * m) • ((k • b i) + a i) = m • (((2 * k) • b i) + (2 • a i))
      simp only [nsmul_eq_mul]; push_cast; ring
    have h_k2m' : mapsRationalSections Φ (m • ((2 * k) • b))
        (m • ((2 * k) • b + 2 • a)) ((2 * m) • (k • b - a)) := by rwa [← he₀, ← he₁]
    have hcard := rational_card_sq_le_of_two_targets Φ h_2k h_k2m'
    haveI := hnonempty (m • ((2 * k) • b))
    have hfpos : 0 < (maxFibre (restrictRationalSectionMap Φ h_2k) : ℝ) :=
      Nat.cast_pos.mpr (maxFibre_pos _)
    have hc₀ := hc_pos_real (m • ((2 * k) • b))
    have hc₁ := hc_pos_real (m • ((2 * k) • b + 2 • a))
    have hc₂ := hc_pos_real (m • ((2 * k) • b - a))
    have hreal : ((divisorSections (m • ((2 * k) • b))).card : ℝ)^2 ≤
        maxFibre (restrictRationalSectionMap Φ h_2k) *
          ((divisorSections (m • ((2 * k) • b + 2 • a))).card *
            (divisorSections (m • ((2 * k) • b - a))).card) := by exact_mod_cast hcard
    have hlog := Real.log_le_log (sq_pos_of_pos hc₀) hreal
    rw [Real.log_pow, Real.log_mul hfpos.ne' (mul_pos hc₁ hc₂).ne', Real.log_mul hc₁.ne' hc₂.ne'] at hlog
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hd : 4 < (2 * logCard (m • ((2 * k) • b)) -
        logCard (m • ((2 * k) • b + 2 • a)) - logCard (m • ((2 * k) • b - a))) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using h_rate
    have hrate' := (lt_div_iff₀ hm2).mp hd
    unfold logCard at hrate'; push_cast at hlog
    linarith only [hsmall, hlog, hrate', hm2]
  · have hΔ_eq : Δ = integerProbe N (b + a) - integerProbe N (b - a) := abs_of_pos hpos_mix
    have hdef : 4 < 2 * integerProbe N ((2 * k) • b) -
        integerProbe N ((2 * k) • b + a) - integerProbe N ((2 * k) • b - 2 • a) := by
      rw [hΔ_eq] at hgap_k; linarith only [hp1, hp2, hp3, hp4, hgap_k]
    have hl₀ := logCard_tateLimit ((2 * k) • b); rw [max_eq_left hmid_pos] at hl₀
    have hl₁ := logCard_tateLimit ((2 * k) • b + a); rw [max_eq_left hp_2k_a.le] at hl₁
    have hl₂ := logCard_tateLimit ((2 * k) • b - 2 • a); rw [max_eq_left hn_2k_2a.le] at hl₂
    have hlim := ((hl₀.const_mul 2).sub hl₁).sub hl₂
    obtain ⟨m, ⟨h_2k, hsmall⟩, h_k2m, h_rate, hm1⟩ :=
      ((hfib_2k 1 one_pos).and_eventually
        (h2m_map.and ((hlim.eventually_const_lt hdef).and (eventually_ge_atTop 1)))).exists
    have he₀ : (2 * m) • (k • b) = m • ((2 * k) • b) := by
      rw [smul_smul, smul_smul, show 2 * m * k = m * (2 * k) by ring]
    have he₂ : (2 * m) • (k • b - a) = m • ((2 * k) • b - 2 • a) := by
      ext i; change (2 * m) • ((k • b i) - a i) = m • (((2 * k) • b i) - (2 • a i))
      simp only [nsmul_eq_mul]; push_cast; ring
    have h_k2m' : mapsRationalSections Φ (m • ((2 * k) • b))
        ((2 * m) • (k • b + a)) (m • ((2 * k) • b - 2 • a)) := by rwa [← he₀, ← he₂]
    have hcard := rational_card_sq_le_of_two_targets Φ h_k2m' h_2k
    rw [← maxFibre_restrictRationalSectionMap_eq Φ h_2k h_k2m'] at hcard
    haveI := hnonempty (m • ((2 * k) • b))
    have hfpos : 0 < (maxFibre (restrictRationalSectionMap Φ h_2k) : ℝ) :=
      Nat.cast_pos.mpr (maxFibre_pos _)
    have hc₀ := hc_pos_real (m • ((2 * k) • b))
    have hc₁ := hc_pos_real (m • ((2 * k) • b + a))
    have hc₂ := hc_pos_real (m • ((2 * k) • b - 2 • a))
    have hreal : ((divisorSections (m • ((2 * k) • b))).card : ℝ)^2 ≤
        maxFibre (restrictRationalSectionMap Φ h_2k) *
          ((divisorSections (m • ((2 * k) • b + a))).card *
            (divisorSections (m • ((2 * k) • b - 2 • a))).card) := by exact_mod_cast hcard
    have hlog := Real.log_le_log (sq_pos_of_pos hc₀) hreal
    rw [Real.log_pow, Real.log_mul hfpos.ne' (mul_pos hc₁ hc₂).ne', Real.log_mul hc₁.ne' hc₂.ne'] at hlog
    have hm2 : 0 < (m : ℝ)^2 := by positivity
    have hd : 4 < (2 * logCard (m • ((2 * k) • b)) -
        logCard (m • ((2 * k) • b + a)) - logCard (m • ((2 * k) • b - 2 • a))) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using h_rate
    have hrate' := (lt_div_iff₀ hm2).mp hd
    unfold logCard at hrate'; push_cast at hlog
    linarith only [hsmall, hlog, hrate', hm2]

private theorem exists_archRadiusLimit {N : ℕ} {v : Fin N → ℤ} (hv : v ≠ 0) :
    ∃ R_inf : ℝ,
      Tendsto (logRadius (packet v) (3 * windowEnd N)) atTop (𝓝 R_inf) ∧
      ∀ k : ℕ, 1 ≤ k →
        Tendsto (fun m : ℕ => radius (m • (k • v)) / (m : ℝ)^2) atTop (𝓝 ((k : ℝ)^2 * R_inf)) ∧
        Tendsto (fun m : ℕ => Real.log (generator (m • (k • v)) : ℝ) / (m : ℝ)^2) atTop
          (𝓝 ((k : ℝ)^2 * (R_inf - integerProbe N v))) := by
  have hs_neg := tendsto_sampledDegree (packet_contDiff v).continuous
    (packet_window v).1 (packet_window v).2 (-(1 / 2))
  have hs_pos := tendsto_sampledDegree (packet_contDiff v).continuous
    (packet_window v).1 (packet_window v).2 (1 / 2)
  have hdf := tendsto_degreeForm (packet_contDiff v) (packet_hasCompactSupport v)
    (packet_window v).1 (packet_window v).2
  have hrad_lim := ((hs_neg.mul hs_pos).const_mul 2).sub hdf
  refine ⟨_, hrad_lim, fun k hk => ?_⟩
  have hkv : k • v ≠ 0 := by
    intro hz
    apply hv
    funext i
    have hi := congrFun hz i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, mul_eq_zero, Int.natCast_eq_zero] at hi
    exact hi.resolve_left (by omega)
  have hres := tendsto_resolution_ray hkv
  have hrad_k : Tendsto (fun m : ℕ => radius (m • (k • v)) / (m : ℝ)^2)
      atTop (𝓝 ((k : ℝ)^2 * _)) := by
    refine ((hrad_lim.comp hres).const_mul ((k : ℝ)^2)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm2 : (m : ℝ)^2 ≠ 0 := by positivity
    have hsm : m • (k • v) = (m * k) • v := smul_smul m k v
    dsimp only [Function.comp_apply, radius]
    rw [hsm, packet_smul v (m * k)]
    unfold logRadius
    rw [sampledDegree_mul, sampledDegree_mul, degreeForm_mul]
    symm
    rw [div_eq_iff hm2]
    push_cast
    ring
  have hdeg_k := tendsto_splineDegree (k • v)
  rw [integerProbe_smul] at hdeg_k
  refine ⟨hrad_k, ?_⟩
  rw [show (k : ℝ)^2 * (_ - integerProbe N v) = (k : ℝ)^2 * _ - (k : ℝ)^2 * integerProbe N v by ring]
  exact (hrad_k.sub hdeg_k).congr fun m => by ring

/-- On `primePair p`, both the archimedean radius rate and the finite-place
log-generator rate grow at least linearly in `√p`, whereas their difference
`Q(primePair p)` is `o(√p)`. Consequently, along `(2mb, 3mb, 4mb)`, the finite-place
log-generator skew `(log d(4mb) - log d(2mb)) / 2` overshoots `7 Q(primePair p) m²`
at all large `p`, preventing any finite-place-only carry schedule from fitting `S(4mb)`. -/
theorem eventually_primePair_finitePlace_skew_overshoots :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ p : ℕ in atTop,
      7 * |integerProbe (p + 1) (primePair p)| < c₀ * Real.sqrt p ∧
      ∀ᶠ m : ℕ in atTop,
        c₀ * Real.sqrt p * (m : ℝ)^2 <
          (Real.log (generator (m • (4 • primePair p)) : ℝ) -
            Real.log (generator (m • (2 • primePair p)) : ℝ)) / 2 := by
  let I_neg := unitAtomMoment (-(1 / 2))
  let I_pos := unitAtomMoment (1 / 2)
  have hI_neg : 0 < I_neg := unitAtomMoment_pos _
  have hI_pos : 0 < I_pos := unitAtomMoment_pos _
  obtain ⟨C_neg, hC_neg0, herr_neg⟩ := bounded_actual_pole_reading_error (by norm_num : -(1 / 2 : ℝ) ≤ 1)
  obtain ⟨C_pos, hC_pos0, herr_pos⟩ := bounded_actual_pole_reading_error (by norm_num : (1 / 2 : ℝ) ≤ 1)
  obtain ⟨J, hJ0, hjet⟩ := uniform_finite_jet_debit
  let c₀ : ℝ := 2 * (I_neg * I_pos)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hsub := tendsto_primePair_degree_div_sqrt.abs
  rw [abs_zero] at hsub
  have hev_deg := hsub.eventually_lt_const (show (0 : ℝ) < c₀ / 14 by positivity)
  obtain ⟨P₁, hP₁⟩ := exists_nat_gt ((8 * J / c₀) ^ 2 + 1)
  filter_upwards [hev_deg, eventually_ge_atTop (max P₁ 2)] with p hp_deg hp_ge
  have hp_pos : 0 < p := by omega
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp_pos)
  rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp] at hp_deg
  refine ⟨by linarith only [hp_deg, mul_pos hc₀ hsp], ?_⟩
  let bp := primePair p
  have hbp_ne : bp ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    simp only [bp, primePair, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true] at h0
    split_ifs at h0 <;> omega
  have hbp_nonneg (i : Fin (p + 1)) : 0 ≤ bp i := by
    simp only [bp, primePair, Pi.add_apply, Pi.single_apply]
    split_ifs <;> decide
  have hmom_val (t : ℝ) : conductorExpMoment t bp = Real.exp (t * Real.log p) + 1 := by
    have hd : ((p - 1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp_pos]; push_cast; ring
    unfold conductorExpMoment bp primePair
    simp only [Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_one,
      Int.cast_zero, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      mem_univ, if_true, Fin.val_zero, Nat.cast_zero, zero_add, hd, Real.log_one, mul_zero,
      Real.exp_zero]
  have hvar_bp : (∑ i : Fin (p + 1), |(bp i : ℝ)|) = 2 := by
    have hn (i : Fin (p + 1)) : 0 ≤ (bp i : ℝ) := by exact_mod_cast hbp_nonneg i
    have h0 := hmom_val 0
    simp only [conductorExpMoment, zero_mul, Real.exp_zero, mul_one, one_add_one_eq_two] at h0
    simpa only [abs_of_nonneg (hn _)] using h0
  have hexp_half : Real.exp ((1 / 2 : ℝ) * Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr hp_pos), mul_comm]
  obtain ⟨R_inf, hrad_lim, hk_lim⟩ := exists_archRadiusLimit hbp_ne
  let L := 3 * windowEnd (p + 1)
  let low (m : ℕ) : ℝ := 2 * ((I_neg - C_neg / (m : ℝ)) * (I_pos * Real.sqrt p - C_pos / (m : ℝ))) - 4 * J
  have hzero (C : ℝ) : Tendsto (fun m : ℕ => C / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlow_lim : Tendsto low atTop (𝓝 (c₀ * Real.sqrt p - 4 * J)) := by
    have h₁ : Tendsto (fun m : ℕ => I_neg - C_neg / (m : ℝ)) atTop (𝓝 I_neg) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub (hzero C_neg)
    have h₂ : Tendsto (fun m : ℕ => I_pos * Real.sqrt p - C_pos / (m : ℝ)) atTop (𝓝 (I_pos * Real.sqrt p)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub (hzero C_pos)
    have hprod := ((h₁.mul h₂).const_mul 2).sub tendsto_const_nhds
    simpa only [low, c₀, mul_assoc] using hprod
  have hev_bound : ∀ᶠ m : ℕ in atTop,
      low m ≤ logRadius (packet bp) L (resolution (m • bp)) := by
    filter_upwards [(hzero C_neg).eventually_lt_const hI_neg,
      (hzero C_pos).eventually_lt_const (mul_pos hI_pos hsp),
      eventually_ge_atTop 1] with m hm_neg hm_pos_c hm1
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
    have hmbp_ne : m • bp ≠ 0 := by
      intro hz; apply hbp_ne; funext i
      have hi := congrFun hz i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, mul_eq_zero, Int.natCast_eq_zero] at hi
      exact hi.resolve_left (by omega)
    have hcm (t : ℝ) : conductorExpMoment t (m • bp) = (m : ℝ) * (Real.exp (t * Real.log p) + 1) := by
      rw [← hmom_val t]
      unfold conductorExpMoment
      simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← mul_sum]
    have he_neg := (abs_le.mp (herr_neg (p + 1) (m • bp))).1
    rw [packet_smul bp m, sampledDegree_mul, hcm] at he_neg
    have hs_neg_ge : I_neg - C_neg / (m : ℝ) ≤ sampledDegree (packet bp) L (resolution (m • bp)) (-(1 / 2)) := by
      have hexp_pos : 0 < Real.exp (-(1 / 2 : ℝ) * Real.log p) := Real.exp_pos _
      have hmul_ge : (m : ℝ) * I_neg - C_neg ≤ (m : ℝ) * sampledDegree (packet bp) L (resolution (m • bp)) (-(1 / 2)) := by
        nlinarith only [he_neg, hm_pos, hI_neg, hexp_pos]
      have hdiv := div_le_div_of_nonneg_right hmul_ge hm_pos.le
      rw [sub_div, mul_div_cancel_left₀ _ hm_pos.ne', mul_div_cancel_left₀ _ hm_pos.ne'] at hdiv
      exact hdiv
    have he_pos := (abs_le.mp (herr_pos (p + 1) (m • bp))).1
    rw [packet_smul bp m, sampledDegree_mul, hcm, hexp_half] at he_pos
    have hs_pos_ge : I_pos * Real.sqrt p - C_pos / (m : ℝ) ≤
        sampledDegree (packet bp) L (resolution (m • bp)) (1 / 2) := by
      have hmul_ge : (m : ℝ) * (I_pos * Real.sqrt p) - C_pos ≤
          (m : ℝ) * sampledDegree (packet bp) L (resolution (m • bp)) (1 / 2) := by
        nlinarith only [he_pos, hm_pos, hI_pos]
      have hdiv := div_le_div_of_nonneg_right hmul_ge hm_pos.le
      rw [sub_div, mul_div_cancel_left₀ _ hm_pos.ne', mul_div_cancel_left₀ _ hm_pos.ne'] at hdiv
      exact hdiv
    have hprod := mul_le_mul hs_neg_ge hs_pos_ge (by linarith only [hm_pos_c])
      ((by linarith only [hm_neg] : 0 ≤ I_neg - C_neg / (m : ℝ)).trans hs_neg_ge)
    have hj := hjet (p + 1) bp L (resolution (m • bp)) (resolution_pos hmbp_ne)
    rw [hvar_bp] at hj
    dsimp only [low, logRadius]
    linarith only [hprod, hj]
  have hR_inf_ge : c₀ * Real.sqrt p - 4 * J ≤ R_inf := by
    by_contra! hlt
    let mid := (R_inf + (c₀ * Real.sqrt p - 4 * J)) / 2
    obtain ⟨m, hm_lo, hm_hi, hm_le⟩ :=
      ((hlow_lim.eventually_const_lt (show mid < c₀ * Real.sqrt p - 4 * J by dsimp [mid]; linarith)).and
        (((hrad_lim.comp (tendsto_resolution_ray hbp_ne)).eventually_lt_const
          (show R_inf < mid by dsimp [mid]; linarith)).and hev_bound)).exists
    dsimp only [Function.comp_apply] at hm_hi
    linarith only [hm_lo, hm_hi, hm_le]
  have h4J_lt : 4 * J < c₀ / 2 * Real.sqrt p := by
    have hP₁_le : (P₁ : ℝ) ≤ p := by exact_mod_cast (le_max_left P₁ 2).trans hp_ge
    have hsq_lt : (8 * J / c₀) ^ 2 < (p : ℝ) := by linarith only [hP₁, hP₁_le]
    have h8 : 8 * J / c₀ < Real.sqrt p := by
      rcases le_or_gt 0 (8 * J / c₀) with hnn | hneg
      · rw [← Real.sqrt_sq hnn]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq_lt
      · exact hneg.trans hsp
    have hmul := (div_lt_iff₀ hc₀).mp h8
    linarith only [hmul]
  have hskew_lim := (((hk_lim 4 (by decide)).2.sub (hk_lim 2 (by decide)).2).div_const 2)
  have hlim_gt : c₀ * Real.sqrt p <
      ((4 : ℕ) ^ 2 * (R_inf - integerProbe (p + 1) bp) -
        (2 : ℕ) ^ 2 * (R_inf - integerProbe (p + 1) bp)) / 2 := by
    push_cast
    linarith only [hR_inf_ge, h4J_lt, hp_deg, le_abs_self (integerProbe (p + 1) bp), mul_pos hc₀ hsp]
  filter_upwards [hskew_lim.eventually_const_lt hlim_gt, eventually_ge_atTop 1] with m hm hm1
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hd : c₀ * Real.sqrt p <
      ((Real.log (generator (m • (4 • bp)) : ℝ) -
        Real.log (generator (m • (2 • bp)) : ℝ)) / 2) / (m : ℝ)^2 := by
    convert hm using 1
    ring
  exact (lt_div_iff₀ hm2).mp hd

/-- Any centered carry schedule `K_m` whose logarithmic scale exceeds `7 Q(b)`
eventually overflows `divisorSections (m • (4 • b))` along `(2mb, 3mb, 4mb)`. -/
theorem eventually_not_centeredCarry_of_skew_gt_seven {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {K : ℕ → ℕ} {μ : ℝ}
    (hK : Tendsto (fun m : ℕ => Real.log (2 * K m + 1 : ℕ) / (m : ℝ)^2) atTop (𝓝 μ))
    (hμ : 7 * integerProbe N b < μ) :
    ∀ᶠ m : ℕ in atTop,
      ¬ mapsDivisorSections (centeredCarry (K m))
          (m • (3 • b)) (m • (4 • b)) (m • (2 • b)) := by
  have hb3 : 0 < integerProbe N (3 • b) := by rw [integerProbe_smul]; positivity
  have hb4 : 0 < integerProbe N (4 • b) := by rw [integerProbe_smul]; positivity
  have hr₃ := tendsto_log_sectionRadius hb3
  have hr₄ := tendsto_log_sectionRadius hb4
  rw [integerProbe_smul] at hr₃ hr₄
  have hdiff := (hK.add hr₃).sub hr₄
  have hev := hdiff.eventually_const_lt
    (show (0 : ℝ) < μ + (3 : ℕ)^2 * integerProbe N b - (4 : ℕ)^2 * integerProbe N b by
      push_cast; linarith)
  have hr3_pos : ∀ᶠ m : ℕ in atTop, 1 ≤ sectionRadius (m • (3 • b)) := by
    filter_upwards [(tendsto_log_sectionRadius hb3).eventually_const_lt (half_lt_self hb3),
      eventually_ge_atTop 1] with m hm _
    by_contra! h0
    have hz : sectionRadius (m • (3 • b)) = 0 := by omega
    rw [hz, Nat.cast_zero, Real.log_zero, zero_div] at hm
    linarith [half_pos hb3]
  filter_upwards [hev, hr3_pos, eventually_ge_atTop 1] with m hm hr3 hm1 hmaps
  have hbounds := (bounds_of_centeredCarry_maps_Icc fun z₁ hz₁ z₂ hz₂ =>
    hmaps z₁ hz₁ z₂ hz₂).2
  have hmul_le : (2 * K m + 1) * sectionRadius (m • (3 • b)) ≤ sectionRadius (m • (4 • b)) :=
    Nat.le_trans (Nat.le_add_right _ _) hbounds
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hM_pos : 0 < 2 * K m + 1 := by omega
  have hr4_pos : 0 < sectionRadius (m • (4 • b)) :=
    (Nat.mul_pos hM_pos hr3).trans_le hmul_le
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hM_pos hr3))
    (Nat.cast_le.mpr hmul_le)
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr hM_pos).ne' (Nat.cast_pos.mpr hr3).ne'] at hlog
  have hd : 0 < (Real.log (2 * K m + 1 : ℕ) + Real.log (sectionRadius (m • (3 • b))) -
      Real.log (sectionRadius (m • (4 • b)))) / (m : ℝ)^2 := by
    simpa only [add_div, sub_div] using hm
  have hm' := (lt_div_iff₀ hm2).mp hd
  linarith only [hlog, hm']

/-! ### 3. Explicit adelic ternary carry rule on rational section representatives -/

/-- Pre-cardinality Arakelov degree `radius v - log d(v)` combining the archimedean
logarithmic radius and the finite-place contact generator. -/
def arakelovDegree {N : ℕ} (v : Fin N → ℤ) : ℝ :=
  radius v - Real.log (generator v : ℝ)

/-- Half-difference of the outer Arakelov degrees; depends neither on the midpoint `v₀`
nor on any section cardinality. -/
def outerAdelicSkew {N : ℕ} (v₁ v₂ : Fin N → ℤ) : ℝ :=
  (arakelovDegree v₁ - arakelovDegree v₂) / 2

/-- Orientation of the outer Arakelov skew (`true` when `0 ≤ outerAdelicSkew v₁ v₂`). -/
def adelicSkewNonneg {N : ℕ} (v₁ v₂ : Fin N → ℤ) : Bool := by
  classical
  exact if 0 ≤ outerAdelicSkew v₁ v₂ then true else false

theorem adelicSkewNonneg_eq_true {N : ℕ} {v₁ v₂ : Fin N → ℤ}
    (h : 0 ≤ outerAdelicSkew v₁ v₂) : adelicSkewNonneg v₁ v₂ = true := by
  unfold adelicSkewNonneg
  exact if_pos h

theorem adelicSkewNonneg_eq_false {N : ℕ} {v₁ v₂ : Fin N → ℤ}
    (h : outerAdelicSkew v₁ v₂ < 0) : adelicSkewNonneg v₁ v₂ = false := by
  unfold adelicSkewNonneg
  exact if_neg (not_le.mpr h)

/-- Ternary carry order `τ = ⌊|outerAdelicSkew v₁ v₂| / log 3⌋₊`. -/
def ternaryCarryOrder {N : ℕ} (v₁ v₂ : Fin N → ℤ) : ℕ :=
  ⌊|outerAdelicSkew v₁ v₂| / Real.log 3⌋₊

/-- Half-modulus `K_τ = (3^τ - 1) / 2` satisfying `2 K_τ + 1 = 3^τ`. -/
def ternaryHalfMod (τ : ℕ) : ℕ :=
  (3 ^ τ - 1) / 2

theorem two_mul_ternaryHalfMod_add_one (τ : ℕ) :
    2 * ternaryHalfMod τ + 1 = 3 ^ τ := by
  unfold ternaryHalfMod
  have hmod : 3 ^ τ % 2 = 1 := by
    induction τ with
    | zero => rfl
    | succ n ih => rw [pow_succ, Nat.mul_mod, ih]
  have hpos : 1 ≤ 3 ^ τ := Nat.one_le_pow τ 3 (by decide)
  omega

theorem two_mul_ternaryHalfMod_add_one_int (τ : ℕ) :
    2 * (ternaryHalfMod τ : ℤ) + 1 = (3 : ℤ) ^ τ := by
  exact_mod_cast two_mul_ternaryHalfMod_add_one τ

/-- Oriented base-`3^τ` Euclidean carry encoder on integer lattice coordinates. -/
def orientedTernaryEncode (posSkew : Bool) (τ : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  if posSkew then centeredCarry (ternaryHalfMod τ) z
  else Prod.swap (centeredCarry (ternaryHalfMod τ) z)

/-- Oriented base-`3^τ` Euclidean carry decoder on integer lattice coordinates. -/
def orientedTernaryDecode (posSkew : Bool) (τ : ℕ) (w : ℤ × ℤ) : ℤ × ℤ :=
  if posSkew then centeredCarry (ternaryHalfMod τ) w
  else centeredCarry (ternaryHalfMod τ) (Prod.swap w)

theorem orientedTernaryDecode_encode (posSkew : Bool) (τ : ℕ) (z : ℤ × ℤ) :
    orientedTernaryDecode posSkew τ (orientedTernaryEncode posSkew τ z) = z := by
  cases posSkew <;> simp only [orientedTernaryDecode, orientedTernaryEncode,
    Bool.false_eq_true, ↓reduceIte, Prod.swap_swap] <;>
    exact centeredCarry_involutive _ _

theorem orientedTernaryEncode_decode (posSkew : Bool) (τ : ℕ) (w : ℤ × ℤ) :
    orientedTernaryEncode posSkew τ (orientedTernaryDecode posSkew τ w) = w := by
  cases posSkew
  · simp only [orientedTernaryDecode, orientedTernaryEncode, Bool.false_eq_true, ↓reduceIte]
    rw [centeredCarry_involutive, Prod.swap_swap]
  · simp only [orientedTernaryDecode, orientedTernaryEncode, ↓reduceIte]
    exact centeredCarry_involutive _ _

theorem orientedTernaryEncode_bijective (posSkew : Bool) (τ : ℕ) :
    Function.Bijective (orientedTernaryEncode posSkew τ) :=
  ⟨fun _ _ h => by
    have hd := congrArg (orientedTernaryDecode posSkew τ) h
    rwa [orientedTernaryDecode_encode, orientedTernaryDecode_encode] at hd,
   fun w => ⟨orientedTernaryDecode posSkew τ w, orientedTernaryEncode_decode posSkew τ w⟩⟩

/-- Explicit single arithmetic encoder on rational section representatives
`(s₁, s₂) ∈ d(v₀) ℤ × d(v₀) ℤ → d(v₁) ℤ × d(v₂) ℤ`. -/
def adelicSectionEncode {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) (s : ℚ × ℚ) : ℚ × ℚ :=
  let w := orientedTernaryEncode (adelicSkewNonneg v₁ v₂) (ternaryCarryOrder v₁ v₂)
    (sectionCoord v₀ s.1, sectionCoord v₀ s.2)
  (sectionRep v₁ w.1, sectionRep v₂ w.2)

/-- Explicit arithmetic decoder on rational section representatives
`(t₁, t₂) ∈ d(v₁) ℤ × d(v₂) ℤ → d(v₀) ℤ × d(v₀) ℤ`. -/
def adelicSectionDecode {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) (t : ℚ × ℚ) : ℚ × ℚ :=
  let z := orientedTernaryDecode (adelicSkewNonneg v₁ v₂) (ternaryCarryOrder v₁ v₂)
    (sectionCoord v₁ t.1, sectionCoord v₂ t.2)
  (sectionRep v₀ z.1, sectionRep v₀ z.2)

theorem adelicSectionEncode_inSectionLattice {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) (s : ℚ × ℚ) :
    inSectionLattice v₁ (adelicSectionEncode v₀ v₁ v₂ s).1 ∧
      inSectionLattice v₂ (adelicSectionEncode v₀ v₁ v₂ s).2 :=
  ⟨inSectionLattice_sectionRep v₁ _, inSectionLattice_sectionRep v₂ _⟩

theorem adelicSectionDecode_inSectionLattice {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) (t : ℚ × ℚ) :
    inSectionLattice v₀ (adelicSectionDecode v₀ v₁ v₂ t).1 ∧
      inSectionLattice v₀ (adelicSectionDecode v₀ v₁ v₂ t).2 :=
  ⟨inSectionLattice_sectionRep v₀ _, inSectionLattice_sectionRep v₀ _⟩

/-- Exact left-inverse law on the rational section lattice `d(v₀) ℤ × d(v₀) ℤ`. -/
theorem adelicSectionDecode_encode {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) {s : ℚ × ℚ}
    (hs₁ : inSectionLattice v₀ s.1) (hs₂ : inSectionLattice v₀ s.2) :
    adelicSectionDecode v₀ v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s) = s := by
  unfold adelicSectionDecode adelicSectionEncode
  simp only [sectionCoord_sectionRep, Prod.mk.eta, orientedTernaryDecode_encode]
  exact Prod.ext (sectionRep_sectionCoord hs₁) (sectionRep_sectionCoord hs₂)

/-- Exact right-inverse law on `d(v₁) ℤ × d(v₂) ℤ`. -/
theorem adelicSectionEncode_decode {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) {t : ℚ × ℚ}
    (ht₁ : inSectionLattice v₁ t.1) (ht₂ : inSectionLattice v₂ t.2) :
    adelicSectionEncode v₀ v₁ v₂ (adelicSectionDecode v₀ v₁ v₂ t) = t := by
  unfold adelicSectionEncode adelicSectionDecode
  simp only [sectionCoord_sectionRep, Prod.mk.eta, orientedTernaryEncode_decode]
  exact Prod.ext (sectionRep_sectionCoord ht₁) (sectionRep_sectionCoord ht₂)

/-! ### 4. Valuation payment for every ambiguous digit and two-output precision comparison -/

/-- Wide coordinate of an oriented pair (`w.1` when `posSkew = true`, `w.2` when `false`). -/
def wideCoord (posSkew : Bool) (w : ℤ × ℤ) : ℤ :=
  if posSkew then w.1 else w.2

/-- Narrow coordinate of an oriented pair (`w.2` when `posSkew = true`, `w.1` when `false`). -/
def narrowCoord (posSkew : Bool) (w : ℤ × ℤ) : ℤ :=
  if posSkew then w.2 else w.1

theorem wideCoord_encode (posSkew : Bool) (τ : ℕ) (z : ℤ × ℤ) :
    wideCoord posSkew (orientedTernaryEncode posSkew τ z) =
      balRem (ternaryHalfMod τ) z.1 + (3 : ℤ) ^ τ * z.2 := by
  cases posSkew <;> dsimp only [wideCoord, orientedTernaryEncode, Prod.swap, centeredCarry] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, two_mul_ternaryHalfMod_add_one_int]

theorem narrowCoord_encode (posSkew : Bool) (τ : ℕ) (z : ℤ × ℤ) :
    narrowCoord posSkew (orientedTernaryEncode posSkew τ z) =
      balQuot (ternaryHalfMod τ) z.1 := by
  cases posSkew <;> dsimp only [narrowCoord, orientedTernaryEncode, Prod.swap, centeredCarry] <;>
    simp only [Bool.false_eq_true, ↓reduceIte]

/-- Exact base-`3^τ` linear conservation law across the wide and narrow outputs. -/
theorem orientedTernary_linear_conservation (posSkew : Bool) (τ : ℕ) (z : ℤ × ℤ) :
    wideCoord posSkew (orientedTernaryEncode posSkew τ z) +
      (3 : ℤ) ^ τ * narrowCoord posSkew (orientedTernaryEncode posSkew τ z) =
      z.1 + (3 : ℤ) ^ τ * z.2 := by
  rw [wideCoord_encode, narrowCoord_encode, ← two_mul_ternaryHalfMod_add_one_int]
  linarith only [balRem_add_mul_balQuot (ternaryHalfMod τ) z.1]

/-- Exact finite slice of `3^τ` first-coordinate candidates sharing narrow quotient `q`. -/
def narrowSlice (τ : ℕ) (q : ℤ) : Finset ℤ :=
  Finset.Icc ((3 : ℤ) ^ τ * q - ternaryHalfMod τ) ((3 : ℤ) ^ τ * q + ternaryHalfMod τ)

/-- For fixed `z₂` and narrow output `q`, the ambiguous first-coordinate candidates form
`narrowSlice τ q` of exact cardinality `3^τ`. -/
theorem narrowSlice_card_and_mem (τ : ℕ) (q : ℤ) :
    (narrowSlice τ q).card = 3 ^ τ ∧
      ∀ (posSkew : Bool) (z₁ z₂ : ℤ),
        narrowCoord posSkew (orientedTernaryEncode posSkew τ (z₁, z₂)) = q ↔
          z₁ ∈ narrowSlice τ q := by
  have h2K := two_mul_ternaryHalfMod_add_one_int τ
  refine ⟨?_, fun posSkew z₁ z₂ => ?_⟩
  · unfold narrowSlice
    rw [Int.card_Icc]
    have h2K_nat := two_mul_ternaryHalfMod_add_one τ
    omega
  · rw [narrowCoord_encode, narrowSlice, Finset.mem_Icc]
    constructor
    · intro hq
      have hdecomp := balRem_add_mul_balQuot (ternaryHalfMod τ) z₁
      obtain ⟨hr_lo, hr_hi⟩ := balRem_bounds (ternaryHalfMod τ) z₁
      rw [hq, h2K] at hdecomp
      exact ⟨by linarith only [hdecomp, hr_lo], by linarith only [hdecomp, hr_hi]⟩
    · rintro ⟨hlo, hhi⟩
      unfold balQuot
      rw [h2K]
      let M : ℤ := (3 : ℤ) ^ τ
      have hM : 0 < M := by dsimp [M]; positivity
      have hdiv := Int.mul_ediv_add_emod (z₁ + ternaryHalfMod τ) M
      have hm0 := Int.emod_nonneg (z₁ + ternaryHalfMod τ) hM.ne'
      have hmM := Int.emod_lt_of_pos (z₁ + ternaryHalfMod τ) hM
      change (z₁ + ternaryHalfMod τ) / M = q
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (z₁ + ternaryHalfMod τ) / M - q ≤ -1 := by omega
        nlinarith only [hM, hlo, hmM, hdiv, hle]
      · have hge : 1 ≤ (z₁ + ternaryHalfMod τ) / M - q := by omega
        nlinarith only [hM, hhi, hm0, hdiv, hge, h2K]

/-- Two inputs share the same ambiguous carry digit `balRem K_τ z.1` iff their wide
encoded coordinates are congruent modulo `3^τ`. -/
theorem carryDigit_eq_iff_wideCoord_modEq (posSkew : Bool) (τ : ℕ) (z z' : ℤ × ℤ) :
    balRem (ternaryHalfMod τ) z.1 = balRem (ternaryHalfMod τ) z'.1 ↔
      wideCoord posSkew (orientedTernaryEncode posSkew τ z) ≡
        wideCoord posSkew (orientedTernaryEncode posSkew τ z') [ZMOD ((3 : ℤ) ^ τ)] := by
  rw [wideCoord_encode, wideCoord_encode, Int.modEq_iff_dvd]
  let K := ternaryHalfMod τ
  let M : ℤ := (3 : ℤ) ^ τ
  have h2K : 2 * (K : ℤ) + 1 = M := two_mul_ternaryHalfMod_add_one_int τ
  constructor
  · intro heq
    refine ⟨z'.2 - z.2, ?_⟩
    change (balRem K z'.1 + M * z'.2) - (balRem K z.1 + M * z.2) = M * (z'.2 - z.2)
    rw [heq]; ring
  · rintro ⟨c, hc⟩
    obtain ⟨h1_lo, h1_hi⟩ := balRem_bounds K z.1
    obtain ⟨h2_lo, h2_hi⟩ := balRem_bounds K z'.1
    have hrem_dvd : M * (c - (z'.2 - z.2)) = balRem K z'.1 - balRem K z.1 := by
      dsimp only [M, K] at hc ⊢
      linarith only [hc]
    have hM_pos : 0 < M := by dsimp [M]; positivity
    have hcz : c - (z'.2 - z.2) = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : c - (z'.2 - z.2) ≤ -1 := by omega
        nlinarith only [hM_pos, h1_hi, h2_lo, h2K, hrem_dvd, hle]
      · have hge : 1 ≤ c - (z'.2 - z.2) := by omega
        nlinarith only [hM_pos, h1_lo, h2_hi, h2K, hrem_dvd, hge]
    rw [hcz, mul_zero] at hrem_dvd
    linarith only [hrem_dvd]

/-- Wide rational section representative of an encoded rational pair. -/
def wideSection {N : ℕ} (v₁ v₂ : Fin N → ℤ) (t : ℚ × ℚ) : ℚ :=
  if adelicSkewNonneg v₁ v₂ then t.1 else t.2

/-- Generator of the wide outer lattice. -/
def wideGenerator {N : ℕ} (v₁ v₂ : Fin N → ℤ) : ℚ :=
  if adelicSkewNonneg v₁ v₂ then generator v₁ else generator v₂

theorem wideGenerator_pos {N : ℕ} (v₁ v₂ : Fin N → ℤ) : 0 < wideGenerator v₁ v₂ := by
  unfold wideGenerator
  cases adelicSkewNonneg v₁ v₂ <;> exact generator_pos_rat _

/-- Rational-section valuation payment law: two encoded rational section pairs share
the same ambiguous carry digit iff the `3`-adic valuation `ratPrimeVal 3` of their wide
section difference exceeds `ratPrimeVal 3 (wideGenerator v₁ v₂)` by at least `τ`. -/
theorem adelicCarryDigit_paid_iff_threeAdic_valuation {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ)
    (s s' : ℚ × ℚ) :
    balRem (ternaryHalfMod (ternaryCarryOrder v₁ v₂)) (sectionCoord v₀ s.1) =
      balRem (ternaryHalfMod (ternaryCarryOrder v₁ v₂)) (sectionCoord v₀ s'.1) ↔
      (wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s) =
          wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s') ∨
        ratPrimeVal 3 (wideGenerator v₁ v₂) + (ternaryCarryOrder v₁ v₂ : ℤ) ≤
          ratPrimeVal 3
            (wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s') -
              wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s))) := by
  let b := adelicSkewNonneg v₁ v₂
  let τ := ternaryCarryOrder v₁ v₂
  let z := (sectionCoord v₀ s.1, sectionCoord v₀ s.2)
  let z' := (sectionCoord v₀ s'.1, sectionCoord v₀ s'.2)
  have hwide_diff : wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s') -
      wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s) =
      wideGenerator v₁ v₂ *
        ((wideCoord b (orientedTernaryEncode b τ z') -
          wideCoord b (orientedTernaryEncode b τ z) : ℤ) : ℚ) := by
    dsimp only [b, τ, z, z']
    unfold wideSection wideGenerator adelicSectionEncode sectionRep
    cases h : adelicSkewNonneg v₁ v₂ <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte, wideCoord, Int.cast_sub, mul_sub]
  have heq_iff : (wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s) =
      wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s')) ↔
      wideGenerator v₁ v₂ *
        ((wideCoord b (orientedTernaryEncode b τ z') -
          wideCoord b (orientedTernaryEncode b τ z) : ℤ) : ℚ) = 0 := by
    rw [← hwide_diff, sub_eq_zero, eq_comm]
  rw [carryDigit_eq_iff_wideCoord_modEq b τ z z', Int.modEq_iff_dvd]
  have hpv := pow_dvd_int_iff_ratPrimeVal (p := 3) (r := τ) Nat.prime_three
    (wideGenerator_pos v₁ v₂)
    (wideCoord b (orientedTernaryEncode b τ z') - wideCoord b (orientedTernaryEncode b τ z))
  dsimp only [Nat.cast_ofNat] at hpv
  rw [hpv, ← hwide_diff, ← heq_iff]

/-- Simultaneous zero-loss congruence preservation and recovery at **every** modulus `u`
coprime to `3` (`gcd(u, 3) = 1`), once the `3^τ` carry digit is paid. -/
theorem orientedTernary_coprime_zeroLoss_recovery (posSkew : Bool) (τ : ℕ) {u : ℕ}
    (hu : u.Coprime 3) {z z' : ℤ × ℤ}
    (hrem : balRem (ternaryHalfMod τ) z.1 = balRem (ternaryHalfMod τ) z'.1) :
    ((orientedTernaryEncode posSkew τ z).1 ≡ (orientedTernaryEncode posSkew τ z').1 [ZMOD (u : ℤ)] ∧
      (orientedTernaryEncode posSkew τ z).2 ≡ (orientedTernaryEncode posSkew τ z').2 [ZMOD (u : ℤ)]) ↔
      (z.1 ≡ z'.1 [ZMOD (u : ℤ)] ∧ z.2 ≡ z'.2 [ZMOD (u : ℤ)]) := by
  have hpair (w w' : ℤ × ℤ) :
      (w.1 ≡ w'.1 [ZMOD (u : ℤ)] ∧ w.2 ≡ w'.2 [ZMOD (u : ℤ)]) ↔
        (wideCoord posSkew w ≡ wideCoord posSkew w' [ZMOD (u : ℤ)] ∧
          narrowCoord posSkew w ≡ narrowCoord posSkew w' [ZMOD (u : ℤ)]) := by
    cases posSkew <;> simp only [wideCoord, narrowCoord, Bool.false_eq_true, ↓reduceIte, and_comm]
  rw [hpair]
  simp only [Int.modEq_iff_dvd, wideCoord_encode, narrowCoord_encode]
  let K := ternaryHalfMod τ
  have h2K := two_mul_ternaryHalfMod_add_one_int τ
  have hcop_pow : u.Coprime (3 ^ τ) := hu.pow_right τ
  have hbez := Nat.gcd_eq_gcd_ab u (3 ^ τ)
  rw [hcop_pow.gcd_eq_one, Nat.cast_one] at hbez
  have cancel_threePow {x : ℤ} (h : (u : ℤ) ∣ (3 : ℤ) ^ τ * x) : (u : ℤ) ∣ x := by
    obtain ⟨c, hc⟩ := h
    refine ⟨Nat.gcdA u (3 ^ τ) * x + Nat.gcdB u (3 ^ τ) * c, ?_⟩
    have hmul := congrArg (· * x) hbez
    rw [one_mul] at hmul
    push_cast at hmul
    linarith only [hmul, congrArg (Nat.gcdB u (3 ^ τ) * ·) hc]
  have hd1 := balRem_add_mul_balQuot K z.1
  have hd2 := balRem_add_mul_balQuot K z'.1
  rw [h2K] at hd1 hd2
  constructor
  · rintro ⟨hw, hn⟩
    have hw' : (u : ℤ) ∣ (3 : ℤ) ^ τ * (z'.2 - z.2) := by
      convert hw using 1; dsimp only [K]; rw [hrem]; ring
    have hz1 : z'.1 - z.1 = (3 : ℤ) ^ τ * (balQuot K z'.1 - balQuot K z.1) := by
      dsimp only [K] at hd1 hd2 ⊢; linarith only [hd1, hd2, hrem]
    exact ⟨hz1 ▸ hn.mul_left _, cancel_threePow hw'⟩
  · rintro ⟨hz1, hz2⟩
    have hw' : (balRem K z'.1 + (3 : ℤ) ^ τ * z'.2) - (balRem K z.1 + (3 : ℤ) ^ τ * z.2) =
        (3 : ℤ) ^ τ * (z'.2 - z.2) := by dsimp only [K]; rw [hrem]; ring
    have hq_mul : (3 : ℤ) ^ τ * (balQuot K z'.1 - balQuot K z.1) = z'.1 - z.1 := by
      dsimp only [K] at hd1 hd2 ⊢; linarith only [hd1, hd2, hrem]
    exact ⟨hw' ▸ hz2.mul_left _, cancel_threePow (hq_mul ▸ hz1)⟩

/-- Asymmetric `3`-adic zero-waste recovery: knowing the wide coordinate modulo `3^(r + τ)`
and the narrow coordinate modulo `3^(r - min r τ)` uniquely recovers both input coordinates
modulo `3^r` (using `(r + τ) + (r - τ) = 2r` total ternary digits whenever `τ ≤ r`). -/
theorem orientedTernary_threeAdic_asymmetric_recovery (posSkew : Bool) (τ r : ℕ) (z z' : ℤ × ℤ)
    (hw : wideCoord posSkew (orientedTernaryEncode posSkew τ z) ≡
      wideCoord posSkew (orientedTernaryEncode posSkew τ z') [ZMOD ((3 : ℤ) ^ (r + τ))])
    (hn : narrowCoord posSkew (orientedTernaryEncode posSkew τ z) ≡
      narrowCoord posSkew (orientedTernaryEncode posSkew τ z') [ZMOD ((3 : ℤ) ^ (r - min r τ))]) :
    z.1 ≡ z'.1 [ZMOD ((3 : ℤ) ^ r)] ∧ z.2 ≡ z'.2 [ZMOD ((3 : ℤ) ^ r)] ∧
      (τ ≤ r → (r + τ) + (r - min r τ) = 2 * r) := by
  have hw_τ : wideCoord posSkew (orientedTernaryEncode posSkew τ z) ≡
      wideCoord posSkew (orientedTernaryEncode posSkew τ z') [ZMOD ((3 : ℤ) ^ τ)] :=
    hw.of_dvd (pow_dvd_pow (3 : ℤ) (Nat.le_add_left τ r))
  have hrem := (carryDigit_eq_iff_wideCoord_modEq posSkew τ z z').mpr hw_τ
  rw [wideCoord_encode, wideCoord_encode, Int.modEq_iff_dvd] at hw
  rw [narrowCoord_encode, narrowCoord_encode, Int.modEq_iff_dvd] at hn
  simp only [Int.modEq_iff_dvd]
  let K := ternaryHalfMod τ
  have h2K := two_mul_ternaryHalfMod_add_one_int τ
  have hd1 := balRem_add_mul_balQuot K z.1
  have hd2 := balRem_add_mul_balQuot K z'.1
  rw [h2K] at hd1 hd2
  have hz2_mul : (3 : ℤ) ^ τ * (3 : ℤ) ^ r ∣ (3 : ℤ) ^ τ * (z'.2 - z.2) := by
    rw [← pow_add, add_comm τ r]
    convert hw using 1
    rw [hrem]; ring
  have hz2 : (3 : ℤ) ^ r ∣ z'.2 - z.2 :=
    (mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ τ ≠ 0)).mp hz2_mul
  have hz1_eq : z'.1 - z.1 = (3 : ℤ) ^ τ * (balQuot K z'.1 - balQuot K z.1) := by
    dsimp only [K] at hd1 hd2 ⊢; linarith only [hd1, hd2, hrem]
  have hz1_high : (3 : ℤ) ^ (τ + (r - min r τ)) ∣ z'.1 - z.1 := by
    rw [hz1_eq, pow_add]
    exact mul_dvd_mul_left _ hn
  have hz1 : (3 : ℤ) ^ r ∣ z'.1 - z.1 :=
    (pow_dvd_pow (3 : ℤ) (by omega : r ≤ τ + (r - min r τ))).trans hz1_high
  exact ⟨hz1, hz2, fun hle => by omega⟩

/-! ### 5. Asymptotic validity, comparison on `(2b, 3b, 4b)`, and single-rule RH equivalence -/

theorem mapsRationalSections_adelicSectionEncode_iff {N : ℕ} (v₀ v₁ v₂ : Fin N → ℤ) :
    mapsRationalSections (adelicSectionEncode v₀ v₁ v₂) v₀ v₁ v₂ ↔
      mapsDivisorSections
        (orientedTernaryEncode (adelicSkewNonneg v₁ v₂) (ternaryCarryOrder v₁ v₂)) v₀ v₁ v₂ := by
  have hd₀ : 0 < (generator v₀ : ℝ) := by exact_mod_cast generator_pos_rat v₀
  have hd₁ : 0 < (generator v₁ : ℝ) := by exact_mod_cast generator_pos_rat v₁
  have hd₂ : 0 < (generator v₂ : ℝ) := by exact_mod_cast generator_pos_rat v₂
  constructor
  · intro h z₁ hz₁ z₂ hz₂
    have hs₁ : sectionRep v₀ z₁ ∈ rationalSections v₀ := Finset.mem_map.mpr ⟨z₁, hz₁, rfl⟩
    have hs₂ : sectionRep v₀ z₂ ∈ rationalSections v₀ := Finset.mem_map.mpr ⟨z₂, hz₂, rfl⟩
    obtain ⟨hm₁, hm₂⟩ := h _ hs₁ _ hs₂
    rw [mem_rationalSections_iff] at hm₁ hm₂
    unfold adelicSectionEncode at hm₁ hm₂
    simp only [sectionCoord_sectionRep] at hm₁ hm₂
    refine ⟨(mem_smallSections hd₁ _).mpr ?_, (mem_smallSections hd₂ _).mpr ?_⟩
    · simpa only [sectionRep, Rat.cast_mul, Rat.cast_intCast] using hm₁.2
    · simpa only [sectionRep, Rat.cast_mul, Rat.cast_intCast] using hm₂.2
  · intro h s₁ hs₁ s₂ hs₂
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_map.mp hs₁
    obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_map.mp hs₂
    dsimp only [Function.Embedding.coeFn_mk]
    obtain ⟨hw₁, hw₂⟩ := h z₁ hz₁ z₂ hz₂
    unfold adelicSectionEncode
    simp only [sectionCoord_sectionRep]
    exact ⟨Finset.mem_map.mpr ⟨_, hw₁, rfl⟩, Finset.mem_map.mpr ⟨_, hw₂, rfl⟩⟩

theorem maxFibre_adelicSectionEncode_eq_one {N : ℕ} {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsRationalSections (adelicSectionEncode v₀ v₁ v₂) v₀ v₁ v₂) :
    maxFibre (restrictRationalSectionMap (adelicSectionEncode v₀ v₁ v₂) h) = 1 := by
  have hinj : Function.Injective (restrictRationalSectionMap (adelicSectionEncode v₀ v₁ v₂) h) := by
    intro p q hpq
    simp only [restrictRationalSectionMap, Prod.ext_iff, Subtype.ext_iff] at hpq
    have hp₁ := (mem_rationalSections_iff v₀ p.1.val).mp p.1.property
    have hp₂ := (mem_rationalSections_iff v₀ p.2.val).mp p.2.property
    have hq₁ := (mem_rationalSections_iff v₀ q.1.val).mp q.1.property
    have hq₂ := (mem_rationalSections_iff v₀ q.2.val).mp q.2.property
    have hdec := congrArg (adelicSectionDecode v₀ v₁ v₂) (Prod.ext hpq.1 hpq.2)
    rw [adelicSectionDecode_encode v₀ v₁ v₂ hp₁.1 hp₂.1,
      adelicSectionDecode_encode v₀ v₁ v₂ hq₁.1 hq₂.1] at hdec
    exact Prod.ext (Subtype.ext (Prod.ext_iff.mp hdec).1) (Subtype.ext (Prod.ext_iff.mp hdec).2)
  haveI : Nonempty ↥(rationalSections v₀) := by
    have hc : 0 < (rationalSections v₀).card := by
      rw [card_rationalSections, divisorSections, card_smallSections]; omega
    exact Finset.Nonempty.to_subtype (Finset.card_pos.mp hc)
  exact le_antisymm ((maxFibre_le_one_iff_injective _).mpr hinj) (maxFibre_pos _)

/-- At `v₁ = v₂ = v₀`, `adelicSectionEncode v₀ v₀ v₀` is the identity on `rationalSections v₀²`
for every divisor `v₀` (including `Q(v₀) ≤ 0`). -/
theorem adelicSectionEncode_self_mapsRationalSections {N : ℕ} (v₀ : Fin N → ℤ) :
    mapsRationalSections (adelicSectionEncode v₀ v₀ v₀) v₀ v₀ v₀ := by
  rw [mapsRationalSections_adelicSectionEncode_iff]
  have hskew : outerAdelicSkew v₀ v₀ = 0 := by unfold outerAdelicSkew; ring
  have hb : adelicSkewNonneg v₀ v₀ = true := adelicSkewNonneg_eq_true (by rw [hskew])
  have hτ : ternaryCarryOrder v₀ v₀ = 0 := by unfold ternaryCarryOrder; rw [hskew]; simp
  have hK : ternaryHalfMod 0 = 0 := rfl
  intro z₁ hz₁ z₂ hz₂
  rw [hb, hτ]
  unfold orientedTernaryEncode centeredCarry balRem balQuot
  rw [hK]
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, add_zero, sub_zero, one_mul,
    Int.emod_one, Int.ediv_one, ↓reduceIte]
  exact ⟨hz₂, hz₁⟩

theorem tendsto_outerAdelicSkew {N : ℕ} (v₁ v₂ : Fin N → ℤ) :
    Tendsto (fun m : ℕ => outerAdelicSkew (m • v₁) (m • v₂) / (m : ℝ)^2) atTop
      (𝓝 ((integerProbe N v₁ - integerProbe N v₂) / 2)) := by
  have h₁ := tendsto_splineDegree v₁
  have h₂ := tendsto_splineDegree v₂
  refine ((h₁.sub h₂).div_const 2).congr fun m => ?_
  unfold outerAdelicSkew arakelovDegree
  ring

theorem tendsto_ternaryCarryScale {N : ℕ} (v₁ v₂ : Fin N → ℤ) :
    Tendsto (fun m : ℕ =>
      Real.log (2 * ternaryHalfMod (ternaryCarryOrder (m • v₁) (m • v₂)) + 1 : ℕ) / (m : ℝ)^2)
      atTop (𝓝 (|integerProbe N v₁ - integerProbe N v₂| / 2)) := by
  have hskew_abs : Tendsto (fun m : ℕ => |outerAdelicSkew (m • v₁) (m • v₂)| / (m : ℝ)^2) atTop
      (𝓝 (|integerProbe N v₁ - integerProbe N v₂| / 2)) := by
    have habs := (tendsto_outerAdelicSkew v₁ v₂).abs
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
    refine habs.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [abs_div, abs_of_pos (by positivity : 0 < (m : ℝ)^2)]
  have hzero : Tendsto (fun m : ℕ => Real.log 3 / (m : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hskew_abs.sub hzero) hskew_abs ?_ ?_
  · filter_upwards with m
    rw [← sub_div]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    rw [two_mul_ternaryHalfMod_add_one, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    have hlt := Nat.lt_floor_add_one (|outerAdelicSkew (m • v₁) (m • v₂)| / Real.log 3)
    have hmul := (div_lt_iff₀ hlog3).mp hlt
    dsimp only [ternaryCarryOrder]
    linarith only [hmul]
  · filter_upwards with m
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    rw [two_mul_ternaryHalfMod_add_one, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    have hle := Nat.floor_le (div_nonneg (abs_nonneg (outerAdelicSkew (m • v₁) (m • v₂))) hlog3.le)
    exact (le_div_iff₀ hlog3).mp hle

/-- Whenever `0 < Q(v₀), Q(v₁), Q(v₂)` and `2 Q(v₀) < Q(v₁) + Q(v₂)`, the single
rule `adelicSectionEncode` eventually maps `rationalSections (m • v₀)²` into
`rationalSections (m • v₁) × rationalSections (m • v₂)` across all skew signs
(`Q(v₁) > Q(v₂)`, `Q(v₁) < Q(v₂)`, and `Q(v₁) = Q(v₂)`). -/
theorem eventually_adelicSectionEncode_mapsRationalSections {N : ℕ} {v₀ v₁ v₂ : Fin N → ℤ}
    (hv₀ : 0 < integerProbe N v₀) (hv₁ : 0 < integerProbe N v₁) (hv₂ : 0 < integerProbe N v₂)
    (hsum : 2 * integerProbe N v₀ < integerProbe N v₁ + integerProbe N v₂) :
    ∀ᶠ m : ℕ in atTop,
      mapsRationalSections
        (adelicSectionEncode (m • v₀) (m • v₁) (m • v₂)) (m • v₀) (m • v₁) (m • v₂) := by
  let K (m : ℕ) := ternaryHalfMod (ternaryCarryOrder (m • v₁) (m • v₂))
  have hK := tendsto_ternaryCarryScale v₁ v₂
  rcases lt_trichotomy (integerProbe N v₂) (integerProbe N v₁) with hgt | heq | hlt
  · have hμ : |integerProbe N v₁ - integerProbe N v₂| / 2 =
        (integerProbe N v₁ - integerProbe N v₂) / 2 := by
      rw [abs_of_pos (sub_pos.mpr hgt)]
    rw [hμ] at hK
    have hev_carry := eventually_centeredCarry_sections_of_window hv₀ hv₁ hv₂ hK
      (by linarith) (by linarith)
    have hev_sign := (tendsto_outerAdelicSkew v₁ v₂).eventually_const_lt
      (show (0 : ℝ) < (integerProbe N v₁ - integerProbe N v₂) / 2 by linarith)
    filter_upwards [hev_carry, hev_sign, eventually_ge_atTop 1] with m hm_c hm_s hm1
    rw [mapsRationalSections_adelicSectionEncode_iff]
    have hpos : 0 < outerAdelicSkew (m • v₁) (m • v₂) :=
      (div_pos_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2)).mp hm_s
    rw [adelicSkewNonneg_eq_true hpos.le]
    exact hm_c
  · have hμ : |integerProbe N v₁ - integerProbe N v₂| / 2 = 0 := by rw [heq, sub_self, abs_zero, zero_div]
    rw [hμ] at hK
    have hev₁ := eventually_centeredCarry_sections_of_window hv₀ hv₁ hv₂ hK
      (by linarith) (by linarith)
    have hev₂ := eventually_centeredCarry_sections_of_window hv₀ hv₂ hv₁ hK
      (by linarith) (by linarith)
    filter_upwards [hev₁, hev₂] with m hm₁ hm₂
    rw [mapsRationalSections_adelicSectionEncode_iff]
    intro z₁ hz₁ z₂ hz₂
    cases adelicSkewNonneg (m • v₁) (m • v₂)
    · dsimp only [orientedTernaryEncode, Prod.swap]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨(hm₂ z₁ hz₁ z₂ hz₂).2, (hm₂ z₁ hz₁ z₂ hz₂).1⟩
    · simp only [orientedTernaryEncode, ↓reduceIte]
      exact hm₁ z₁ hz₁ z₂ hz₂
  · have hμ : |integerProbe N v₁ - integerProbe N v₂| / 2 =
        (integerProbe N v₂ - integerProbe N v₁) / 2 := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
    rw [hμ] at hK
    have hev_carry := eventually_centeredCarry_sections_of_window hv₀ hv₂ hv₁ hK
      (by linarith) (by linarith)
    have hev_sign := (tendsto_outerAdelicSkew v₁ v₂).eventually_lt_const
      (show (integerProbe N v₁ - integerProbe N v₂) / 2 < 0 by linarith)
    filter_upwards [hev_carry, hev_sign, eventually_ge_atTop 1] with m hm_c hm_s hm1
    rw [mapsRationalSections_adelicSectionEncode_iff]
    have hneg : outerAdelicSkew (m • v₁) (m • v₂) < 0 := by
      have hm2 : 0 < (m : ℝ)^2 := by positivity
      have hm' := (div_lt_iff₀ hm2).mp hm_s
      linarith only [hm']
    rw [adelicSkewNonneg_eq_false hneg]
    intro z₁ hz₁ z₂ hz₂
    dsimp only [orientedTernaryEncode, Prod.swap]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨(hm_c z₁ hz₁ z₂ hz₂).2, (hm_c z₁ hz₁ z₂ hz₂).1⟩

private theorem natModEq_iff_intModEq (M a b : ℕ) :
    a ≡ b [MOD M] ↔ (a : ℤ) ≡ (b : ℤ) [ZMOD (M : ℤ)] := by
  change a % M = b % M ↔ (a : ℤ) % (M : ℤ) = (b : ℤ) % (M : ℤ)
  omega

theorem sectionOrdinal_modEq_iff {d A : ℝ} (x y : ↥(smallSections d A)) (M : ℕ) :
    (sectionOrdinal d A x).val ≡ (sectionOrdinal d A y).val [MOD M] ↔
      x.val ≡ y.val [ZMOD (M : ℤ)] := by
  rw [natModEq_iff_intModEq, Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have hsub := sectionOrdinal_sub y x
  rw [hsub]

theorem inducedDivisorSectionMap_adelicSectionEncode {N : ℕ} {v₀ v₁ v₂ : Fin N → ℤ}
    (h : mapsRationalSections (adelicSectionEncode v₀ v₁ v₂) v₀ v₁ v₂)
    (p : ↥(divisorSections v₀) × ↥(divisorSections v₀)) :
    ((inducedDivisorSectionMap h p).1.val, (inducedDivisorSectionMap h p).2.val) =
      orientedTernaryEncode (adelicSkewNonneg v₁ v₂) (ternaryCarryOrder v₁ v₂)
        (p.1.val, p.2.val) := by
  dsimp [inducedDivisorSectionMap, restrictRationalSectionMap, rationalSectionEquiv,
    adelicSectionEncode]
  simp only [sectionCoord_sectionRep, Prod.mk.eta]

/-- Direct comparison of `adelicSectionEncode` along `(2mb, 3mb, 4mb)` against the
two-output carry obstructions: `adelicSectionEncode` restricts eventually to an
injective `rayProductMap b m` (`maxFibre = 1`) with ternary carry order `τ_m`
(`τ_m log 3 / m² → 6 Q(b)`), satisfying symmetric `jointInversePrecisionLoss` at base `3`
with loss `τ_m`, asymmetric `3`-adic recovery with `(r + τ_m) + (r - τ_m) = 2r` total
digits, and zero-loss recovery at **every** modulus `u` coprime to `3` once the wide
output modulo `3^τ_m` pays the carry digit. -/
theorem adelicRayMap_precision_comparison {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) :
    Tendsto (fun m : ℕ =>
      (ternaryCarryOrder (m • (4 • b)) (m • (2 • b)) : ℝ) * Real.log 3 / (m : ℝ)^2)
      atTop (𝓝 (6 * integerProbe N b)) ∧
    ∀ᶠ m : ℕ in atTop,
      ∃ h : mapsRationalSections
          (adelicSectionEncode (m • (3 • b)) (m • (4 • b)) (m • (2 • b)))
          (m • (3 • b)) (m • (4 • b)) (m • (2 • b)),
        let f : rayProductMap b m := inducedDivisorSectionMap h
        let τ := ternaryCarryOrder (m • (4 • b)) (m • (2 • b))
        maxFibre f = 1 ∧
        jointInversePrecisionLoss (ordinalMap b m f) 3 τ ∧
        ∀ (u : ℕ), u.Coprime 3 → ∀ x y : Fin (rayCard b 3 m) × Fin (rayCard b 3 m),
          (ordinalMap b m f x).1.val ≡ (ordinalMap b m f y).1.val [MOD 3 ^ τ] →
          (((ordinalMap b m f x).1.val ≡ (ordinalMap b m f y).1.val [MOD u] ∧
            (ordinalMap b m f x).2.val ≡ (ordinalMap b m f y).2.val [MOD u]) ↔
            (x.1.val ≡ y.1.val [MOD u] ∧ x.2.val ≡ y.2.val [MOD u])) := by
  have hb3 : 0 < integerProbe N (3 • b) := by rw [integerProbe_smul]; positivity
  have hb4 : 0 < integerProbe N (4 • b) := by rw [integerProbe_smul]; positivity
  have hb2 : 0 < integerProbe N (2 • b) := by rw [integerProbe_smul]; positivity
  have hsum : 2 * integerProbe N (3 • b) < integerProbe N (4 • b) + integerProbe N (2 • b) := by
    rw [integerProbe_smul, integerProbe_smul, integerProbe_smul]; push_cast; linarith
  have hscale : Tendsto (fun m : ℕ =>
      (ternaryCarryOrder (m • (4 • b)) (m • (2 • b)) : ℝ) * Real.log 3 / (m : ℝ)^2)
      atTop (𝓝 (6 * integerProbe N b)) := by
    have hK := tendsto_ternaryCarryScale (4 • b) (2 • b)
    rw [integerProbe_smul, integerProbe_smul] at hK
    have hlim_eq : |((4 : ℕ) : ℝ)^2 * integerProbe N b - ((2 : ℕ) : ℝ)^2 * integerProbe N b| / 2 =
        6 * integerProbe N b := by
      push_cast
      rw [show (4 : ℝ)^2 * integerProbe N b - (2 : ℝ)^2 * integerProbe N b =
          12 * integerProbe N b by ring, abs_of_pos (by positivity)]
      ring
    rw [hlim_eq] at hK
    refine hK.congr fun m => ?_
    rw [two_mul_ternaryHalfMod_add_one, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  refine ⟨hscale, ?_⟩
  have hev_sign := (tendsto_outerAdelicSkew (4 • b) (2 • b)).eventually_const_lt
    (show (0 : ℝ) < (integerProbe N (4 • b) - integerProbe N (2 • b)) / 2 by
      rw [integerProbe_smul, integerProbe_smul]; push_cast; linarith)
  filter_upwards [eventually_adelicSectionEncode_mapsRationalSections hb3 hb4 hb2 hsum,
    hev_sign, eventually_ge_atTop 1] with m hm hm_s hm1
  have hpos : 0 < outerAdelicSkew (m • (4 • b)) (m • (2 • b)) :=
    (div_pos_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2)).mp hm_s
  have hb_true : adelicSkewNonneg (m • (4 • b)) (m • (2 • b)) = true :=
    adelicSkewNonneg_eq_true hpos.le
  refine ⟨hm, ?_⟩
  let f : rayProductMap b m := inducedDivisorSectionMap hm
  let τ := ternaryCarryOrder (m • (4 • b)) (m • (2 • b))
  have hf_fib : maxFibre f = 1 :=
    (maxFibre_inducedDivisorSectionMap hm).trans (maxFibre_adelicSectionEncode_eq_one hm)
  have hf_val (p : ↥(divisorSections (m • (3 • b))) × ↥(divisorSections (m • (3 • b)))) :
      ((f p).1.val, (f p).2.val) = orientedTernaryEncode true τ (p.1.val, p.2.val) := by
    dsimp only [f, τ]
    rw [inducedDivisorSectionMap_adelicSectionEncode hm p, hb_true]
  have hord_mod (M : ℕ) (x y : Fin (rayCard b 3 m) × Fin (rayCard b 3 m)) :
      let px := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm x
      let py := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm y
      ((ordinalMap b m f x).1.val ≡ (ordinalMap b m f y).1.val [MOD M] ↔
        (orientedTernaryEncode true τ (px.1.val, px.2.val)).1 ≡
          (orientedTernaryEncode true τ (py.1.val, py.2.val)).1 [ZMOD (M : ℤ)]) ∧
      ((ordinalMap b m f x).2.val ≡ (ordinalMap b m f y).2.val [MOD M] ↔
        (orientedTernaryEncode true τ (px.1.val, px.2.val)).2 ≡
          (orientedTernaryEncode true τ (py.1.val, py.2.val)).2 [ZMOD (M : ℤ)]) ∧
      (x.1.val ≡ y.1.val [MOD M] ↔ px.1.val ≡ py.1.val [ZMOD (M : ℤ)]) ∧
      (x.2.val ≡ y.2.val [MOD M] ↔ px.2.val ≡ py.2.val [ZMOD (M : ℤ)]) := by
    intro px py
    have h1 := sectionOrdinal_modEq_iff (f px).1 (f py).1 M
    have h2 := sectionOrdinal_modEq_iff (f px).2 (f py).2 M
    have h3 := sectionOrdinal_modEq_iff px.1 py.1 M
    have h4 := sectionOrdinal_modEq_iff px.2 py.2 M
    have hfx1 : (f px).1.val = (orientedTernaryEncode true τ (px.1.val, px.2.val)).1 :=
      congrArg Prod.fst (hf_val px)
    have hfy1 : (f py).1.val = (orientedTernaryEncode true τ (py.1.val, py.2.val)).1 :=
      congrArg Prod.fst (hf_val py)
    have hfx2 : (f px).2.val = (orientedTernaryEncode true τ (px.1.val, px.2.val)).2 :=
      congrArg Prod.snd (hf_val px)
    have hfy2 : (f py).2.val = (orientedTernaryEncode true τ (py.1.val, py.2.val)).2 :=
      congrArg Prod.snd (hf_val py)
    rw [hfx1, hfy1] at h1
    rw [hfx2, hfy2] at h2
    have hx1 : sectionOrdinal _ _ px.1 = x.1 := (rayOrdinal b 3 m).apply_symm_apply x.1
    have hy1 : sectionOrdinal _ _ py.1 = y.1 := (rayOrdinal b 3 m).apply_symm_apply y.1
    have hx2 : sectionOrdinal _ _ px.2 = x.2 := (rayOrdinal b 3 m).apply_symm_apply x.2
    have hy2 : sectionOrdinal _ _ py.2 = y.2 := (rayOrdinal b 3 m).apply_symm_apply y.2
    rw [hx1, hy1] at h3
    rw [hx2, hy2] at h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨hf_fib, ?_, ?_⟩
  · intro r x y hw_mod hn_mod
    obtain ⟨h1, _, h3, h4⟩ := hord_mod (3 ^ (r + τ)) x y
    obtain ⟨_, h2, _, _⟩ := hord_mod (3 ^ (r - min r τ)) x y
    obtain ⟨_, _, h3r, h4r⟩ := hord_mod (3 ^ r) x y
    let px := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm x
    let py := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm y
    have hw_z : wideCoord true (orientedTernaryEncode true τ (px.1.val, px.2.val)) ≡
        wideCoord true (orientedTernaryEncode true τ (py.1.val, py.2.val)) [ZMOD ((3 : ℤ) ^ (r + τ))] := by
      simpa only [wideCoord, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] using h1.mp hw_mod
    have hn_le : 3 ^ (r - min r τ) ∣ 3 ^ (r + τ) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hn_z : narrowCoord true (orientedTernaryEncode true τ (px.1.val, px.2.val)) ≡
        narrowCoord true (orientedTernaryEncode true τ (py.1.val, py.2.val))
          [ZMOD ((3 : ℤ) ^ (r - min r τ))] := by
      simpa only [narrowCoord, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] using
        h2.mp (hn_mod.of_dvd hn_le)
    obtain ⟨hz1, hz2, _⟩ := orientedTernary_threeAdic_asymmetric_recovery true τ r
      (px.1.val, px.2.val) (py.1.val, py.2.val) hw_z hn_z
    exact ⟨h3r.mpr (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz1),
           h4r.mpr (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz2)⟩
  · intro u hu x y hpay
    obtain ⟨hpay1, _, _, _⟩ := hord_mod (3 ^ τ) x y
    obtain ⟨hu1, hu2, hu3, hu4⟩ := hord_mod u x y
    let px := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm x
    let py := ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm y
    have hrem : balRem (ternaryHalfMod τ) px.1.val = balRem (ternaryHalfMod τ) py.1.val := by
      apply (carryDigit_eq_iff_wideCoord_modEq true τ (px.1.val, px.2.val) (py.1.val, py.2.val)).mpr
      simpa only [wideCoord, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] using hpay1.mp hpay
    rw [hu1, hu2, hu3, hu4]
    exact orientedTernary_coprime_zeroLoss_recovery true τ hu hrem

/-- Along `(m(kb), m(kb + a), m(kb - a))` over `0 < Q(b)`, whenever `a = 0` or `0 < Q(a)`,
for all sufficiently large `k` and all sufficiently large `m`, `adelicSectionEncode`
maps `rationalSections (m • (k • b))²` injectively (`maxFibre = 1`) into
`rationalSections (m • (k • b + a)) × rationalSections (m • (k • b - a))` and produces
`0 ≤ midpointExcess (k • b) a m`. -/
theorem eventually_adelicSectionEncode_midpoint_ray {N : ℕ} {b a : Fin N → ℤ}
    (hb : 0 < integerProbe N b) (ha : a = 0 ∨ 0 < integerProbe N a) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      ∃ h : mapsRationalSections
          (adelicSectionEncode (m • (k • b)) (m • (k • b + a)) (m • (k • b - a)))
          (m • (k • b)) (m • (k • b + a)) (m • (k • b - a)),
        maxFibre (restrictRationalSectionMap
          (adelicSectionEncode (m • (k • b)) (m • (k • b + a)) (m • (k • b - a))) h) = 1 ∧
        0 ≤ midpointExcess (k • b) a m := by
  rcases ha with rfl | ha_pos
  · filter_upwards [eventually_ge_atTop 1] with k _
    filter_upwards [eventually_ge_atTop 1] with m _
    have hadd : k • b + (0 : Fin N → ℤ) = k • b := add_zero _
    have hsub : k • b - (0 : Fin N → ℤ) = k • b := sub_zero _
    rw [hadd, hsub]
    have h := adelicSectionEncode_self_mapsRationalSections (m • (k • b))
    have hfib := maxFibre_adelicSectionEncode_eq_one h
    have hex : 0 ≤ midpointExcess (k • b) 0 m := by
      unfold midpointExcess
      rw [hadd, hsub]
      linarith
    exact ⟨h, hfib, hex⟩
  · filter_upwards [eventually_ge_atTop 1, eventually_positive_shift b a hb,
      eventually_positive_shift b (-a) hb] with k hk1 hp_pos hn_pos
    rw [← sub_eq_add_neg] at hn_pos
    have hkb : 0 < integerProbe N (k • b) := by
      rw [integerProbe_smul]; exact mul_pos (by positivity) hb
    have hsum : 2 * integerProbe N (k • b) <
        integerProbe N (k • b + a) + integerProbe N (k • b - a) := by
      have hpar := integerProbe_parallelogram N (k • b) a
      linarith only [hpar, ha_pos]
    filter_upwards [eventually_adelicSectionEncode_mapsRationalSections hkb hp_pos hn_pos hsum,
      eventually_ge_atTop 1] with m hm hm1
    have hfib := maxFibre_adelicSectionEncode_eq_one hm
    have hex := neg_log_maxFibre_le_midpointExcess hm1 (inducedDivisorSectionMap hm)
    rw [maxFibre_inducedDivisorSectionMap, hfib, Nat.cast_one, Real.log_one, zero_div, neg_zero] at hex
    exact ⟨hm, hfib, hex⟩

/-- Cofinal validity of `adelicSectionEncode` across cofinal translations forces `0 ≤ Q(a)`. -/
theorem integerProbe_nonneg_of_cofinal_adelicSectionEncode {N : ℕ} {b a : Fin N → ℤ}
    (hb : 0 < integerProbe N b)
    (h : ∃ᶠ k : ℕ in atTop, ∃ᶠ m : ℕ in atTop,
      mapsRationalSections
        (adelicSectionEncode (m • (k • b)) (m • (k • b + a)) (m • (k • b - a)))
        (m • (k • b)) (m • (k • b + a)) (m • (k • b - a))) :
    0 ≤ integerProbe N a := by
  refine integerProbe_nonneg_of_subquadraticMidpointFibres b a hb (h.mono fun k hk => ?_)
  intro ε hε
  refine hk.mono fun m hm => ⟨inducedDivisorSectionMap hm, ?_⟩
  rw [maxFibre_inducedDivisorSectionMap, maxFibre_adelicSectionEncode_eq_one hm,
    Nat.cast_one, Real.log_one]
  exact mul_nonneg hε.le (sq_nonneg _)

/-- Single-rule unrestricted midpoint test using `adelicSectionEncode` on rational
section representatives. -/
def adelicMidpointTest {P : ℕ} (b : Fin P → ℤ) : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ k : ℕ in atTop,
    let B := k • padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    ∀ᶠ m : ℕ in atTop,
      mapsRationalSections (adelicSectionEncode (m • B) (m • (B + A)) (m • (B - A)))
        (m • B) (m • (B + A)) (m • (B - A))

/-- Over any positive background `b`, the Riemann hypothesis is equivalent to the
single explicit rule `adelicSectionEncode` succeeding on every displacement (either
eventually in `m` with `maxFibre = 1`, or merely cofinally in `m`). -/
theorem riemannHypothesis_iff_singleRule_adelicSectionEncode {P : ℕ} (b : Fin P → ℤ)
    (hb : 0 < integerProbe P b) :
    (RiemannHypothesis ↔ adelicMidpointTest b) ∧
    (RiemannHypothesis ↔ ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ k : ℕ in atTop,
      let B := k • padDivisor (le_max_left P N) b
      let A := padDivisor (le_max_right P N) a
      ∃ᶠ m : ℕ in atTop,
        mapsRationalSections (adelicSectionEncode (m • B) (m • (B + A)) (m • (B - A)))
          (m • B) (m • (B + A)) (m • (B - A))) := by
  have forward (hRH : RiemannHypothesis) (N : ℕ) (a : Fin N → ℤ) :
      ∀ᶠ k : ℕ in atTop,
        let B := k • padDivisor (le_max_left P N) b
        let A := padDivisor (le_max_right P N) a
        ∀ᶠ m : ℕ in atTop,
          mapsRationalSections (adelicSectionEncode (m • B) (m • (B + A)) (m • (B - A)))
            (m • B) (m • (B + A)) (m • (B - A)) := by
    let B₀ := padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    have hb₀ : 0 < integerProbe (max P N) B₀ := by simpa only [B₀, integerProbe_pad] using hb
    have hA : A = 0 ∨ 0 < integerProbe (max P N) A := by
      by_cases h0 : A = 0
      · exact Or.inl h0
      · exact Or.inr (integerProbe_pos_of_rh hRH h0)
    filter_upwards [eventually_adelicSectionEncode_midpoint_ray hb₀ hA] with k hk
    exact hk.mono fun m ⟨hm, _, _⟩ => hm
  have backward (h : ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ k : ℕ in atTop,
      let B := k • padDivisor (le_max_left P N) b
      let A := padDivisor (le_max_right P N) a
      ∃ᶠ m : ℕ in atTop,
        mapsRationalSections (adelicSectionEncode (m • B) (m • (B + A)) (m • (B - A)))
          (m • B) (m • (B + A)) (m • (B - A))) : RiemannHypothesis := by
    apply riemannHypothesis_iff_integerProbes.mpr
    intro N a
    let B₀ := padDivisor (le_max_left P N) b
    let A := padDivisor (le_max_right P N) a
    have hb₀ : 0 < integerProbe (max P N) B₀ := by simpa only [B₀, integerProbe_pad] using hb
    have hA := integerProbe_nonneg_of_cofinal_adelicSectionEncode hb₀ (h N a).frequently
    simpa only [A, integerProbe_pad] using hA
  exact ⟨⟨forward, fun h => backward fun N a => (h N a).mono fun _ hk => hk.frequently⟩,
         ⟨fun hRH N a => (forward hRH N a).mono fun _ hk => hk.frequently, backward⟩⟩

/-- Unconditional two-atom prime background on which the single explicit rule
`adelicSectionEncode` characterizes RH. -/
theorem exists_prime_background_singleRule_adelicSectionEncode :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧ (RiemannHypothesis ↔ adelicMidpointTest b) := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, _⟩ := exists_prime_background_subquadraticMidpointTest
  exact ⟨p, b, hp, hb_eq, hb_pos, (riemannHypothesis_iff_singleRule_adelicSectionEncode b hb_pos).1⟩

#print axioms inSectionLattice_iff_primeValuations
#print axioms not_exists_midpointOnly_subquadratic_rationalSectionMap
#print axioms eventually_primePair_finitePlace_skew_overshoots
#print axioms eventually_not_centeredCarry_of_skew_gt_seven
#print axioms adelicSectionDecode_encode
#print axioms adelicCarryDigit_paid_iff_threeAdic_valuation
#print axioms orientedTernary_coprime_zeroLoss_recovery
#print axioms orientedTernary_threeAdic_asymmetric_recovery
#print axioms adelicRayMap_precision_comparison
#print axioms eventually_adelicSectionEncode_mapsRationalSections
#print axioms riemannHypothesis_iff_singleRule_adelicSectionEncode
#print axioms exists_prime_background_singleRule_adelicSectionEncode

end GaloisForLFunctions.CountingHolography.Sections
