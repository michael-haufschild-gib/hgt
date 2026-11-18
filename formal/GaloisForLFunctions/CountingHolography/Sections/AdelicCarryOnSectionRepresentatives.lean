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
   residue of the wide coordinate modulo `3^τ`; once paid, every coprime modulus
   `u` (`gcd(u, 3) = 1`) recovers `(z₁ mod u, z₂ mod u)` with zero precision loss,
   and `3`-adic recovery uses `(r + τ) + (r - τ) = 2r` total ternary digits.
3. **Asymptotic validity and single-rule RH equivalence:** Whenever `v₁ = v₂ = v₀`
   or `0 < Q(v₀), Q(v₁), Q(v₂)` with `2 Q(v₀) < Q(v₁) + Q(v₂)`, `adelicSectionEncode`
   maps `rationalSections (m • v₀)²` injectively (`maxFibre = 1`) into
   `rationalSections (m • v₁) × rationalSections (m • v₂)` for all large `m`. Over
   the fixed two-atom prime background `b`, RH is equivalent to this single rule
   succeeding across all displacements.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticScatteringHolography

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
    unfold ratPrimeVal at hv
    rw [hf_num] at hv
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
    change sectionCoord v s.val ∈ divisorSections v
    rw [← hzs]; change sectionCoord v (sectionRep v z) ∈ divisorSections v
    rwa [sectionCoord_sectionRep]⟩
  left_inv z := Subtype.ext (sectionCoord_sectionRep v z.val)
  right_inv s := Subtype.ext (by
    obtain ⟨z, _, hzs⟩ := Finset.mem_map.mp s.property
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
  let I₋ := unitAtomMoment (-(1 / 2))
  let I₊ := unitAtomMoment (1 / 2)
  have hI₋ : 0 < I₋ := unitAtomMoment_pos _
  have hI₊ : 0 < I₊ := unitAtomMoment_pos _
  obtain ⟨C₋, hC₋0, herr₋⟩ := bounded_actual_pole_reading_error (by norm_num : -(1 / 2 : ℝ) ≤ 1)
  obtain ⟨C₊, hC₊0, herr₊⟩ := bounded_actual_pole_reading_error (by norm_num : (1 / 2 : ℝ) ≤ 1)
  obtain ⟨J, hJ0, hjet⟩ := uniform_finite_jet_debit
  let c₀ : ℝ := 2 * (I₋ * I₊)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hsub := tendsto_primePair_degree_div_sqrt.abs
  rw [abs_zero] at hsub
  have hev_deg := hsub.eventually_lt_const (show (0 : ℝ) < c₀ / 14 by positivity)
  obtain ⟨P₁, hP₁⟩ := exists_nat_gt (((4 * J + 1) / (I₋ * I₊)) ^ 2)
  filter_upwards [hev_deg, eventually_ge_atTop (max P₁ 2)] with p hp_deg hp_ge
  have hp1 : 1 ≤ p := by omega
  have hp_pos : 0 < p := by omega
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp_pos)
  rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp] at hp_deg
  refine ⟨by linarith only [hp_deg], ?_⟩
  let bp := primePair p
  have hbp_ne : bp ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    simp only [bp, primePair, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true] at h0
    split_ifs at h0 <;> omega
  have hmom_val (t : ℝ) : conductorExpMoment t bp = Real.exp (t * Real.log p) + 1 := by
    have hd : ((p - 1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp_pos]; push_cast; ring
    unfold conductorExpMoment bp primePair
    simp only [Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_one,
      Int.cast_zero, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      mem_univ, if_true, Fin.val_zero, Nat.cast_zero, zero_add, hd, Real.log_one, mul_zero,
      Real.exp_zero]
  have hexp_half : Real.exp ((1 / 2 : ℝ) * Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr hp_pos), mul_comm]
  let L := 3 * windowEnd (p + 1)
  have hL1 : 1 ≤ windowEnd (p + 1) := (packet_window bp).1
  have hs_lim (t : ℝ) :
      Tendsto (fun m : ℕ => sampledDegree (packet (m • bp)) L (resolution (m • bp)) t / (m : ℝ))
        atTop (𝓝 (I₋ * 0 + unitAtomMoment t * conductorExpMoment t bp)) := by
    rw [zero_mul, zero_add]
    have hzero : Tendsto (fun m : ℕ => (if t = 1 / 2 then C₊ else C₋) / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hbnd (t' : ℝ) (ht' : t' ≤ 1) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
          |sampledDegree (packet (m • bp)) L (resolution (m • bp)) t' / (m : ℝ) -
            unitAtomMoment t' * conductorExpMoment t' bp| ≤ C / (m : ℝ) := by
      obtain ⟨C, hC, he⟩ := bounded_actual_pole_reading_error ht'
      refine ⟨C, hC, fun m hm => ?_⟩
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hcm : conductorExpMoment t' (m • bp) = (m : ℝ) * conductorExpMoment t' bp := by
        unfold conductorExpMoment
        simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← mul_sum]
      have h1 := he (p + 1) (m • bp)
      rw [hcm] at h1
      rw [← abs_of_pos hm_pos, ← abs_div, sub_div, mul_left_comm (unitAtomMoment t') (m : ℝ),
        mul_div_cancel_left₀ _ hm_pos.ne']
      exact div_le_div_of_nonneg_right h1 hm_pos.le
    -- Unused general `t`; we only need `t = -(1/2)` and `t = 1/2` below.
    sorry
  sorry
