import GaloisForLFunctions.HTGeometry.CompactAbelianPeterWeyl
import GaloisForLFunctions.HTGeometry.CompactGroupMetricReturnLaw
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Topological generators of a compact connected abelian group

Two structural facts about a compact connected second-countable abelian group `G`.

*Divisibility.*  If the `n`-th power map were not surjective its closed image would be a proper
closed subgroup, and a nontrivial character of the quotient would pull back to a character of `G`
with values in the `n`-th roots of unity.  Connectedness forces such a character to be trivial, so
`G` is divisible and hence `RootableBy G ℤ`; the integer power maps then preserve Haar measure.

*Almost every element generates.*  A nontrivial character of a connected group has infinite image,
its fibres are translates of its kernel and so all have the same Haar measure, and therefore the
kernel is null.  Distinct characters are orthonormal in the separable Hilbert space `L²` of the
Haar probability measure, so there are only countably many of them.  An element that fails to
generate a dense subgroup is killed by a nontrivial character, so the non-generators form a
countable union of null sets.

Together with the measure-budget mechanism of `CompactGroupMetricReturnLaw`, this produces a
topological generator whose first `L` powers avoid any target of measure smaller than `1/L`.
-/

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [hBorelG : BorelSpace G]
  [hSecondG : SecondCountableTopology G]

/-- Multiplicative form of Peter–Weyl for compact abelian groups. -/
theorem exists_character_ne_one_mul {g : G} (hg : g ≠ 1) :
    ∃ χ : G → ℂ, Continuous χ ∧ (∀ a b : G, χ (a * b) = χ a * χ b) ∧
      (∀ a, ‖χ a‖ = 1) ∧ χ g ≠ 1 := by
  letI : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
  letI : SecondCountableTopology (Additive G) := ‹SecondCountableTopology G›
  haveI : T2Space (Additive G) := ‹T2Space G›
  haveI : BorelSpace (Additive G) := ‹BorelSpace G›
  have hg' : (Additive.ofMul g) ≠ 0 := hg
  obtain ⟨χ, h1, h2, h3, h4⟩ :=
    GaloisForLFunctions.CompactAbelian.exists_character_ne_one (G := Additive G) hg'
  exact ⟨fun x => χ (Additive.ofMul x), h1, fun a b => h2 a b, fun a => h3 a, h4⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem char_one_eq_one {χ : G → ℂ} (hmul : ∀ a b : G, χ (a * b) = χ a * χ b)
    (hnorm : ∀ a, ‖χ a‖ = 1) : χ 1 = 1 := by
  have h := hmul 1 1
  rw [one_mul] at h
  have hne : χ 1 ≠ 0 := by
    intro h0
    have := hnorm 1
    rw [h0] at this
    simp at this
  field_simp at h
  exact h.symm

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- A continuous character of a connected group whose values are `n`-th roots of unity is
trivial. -/
theorem character_eq_one_of_connected [ConnectedSpace G] {χ : G → ℂ} (hcont : Continuous χ)
    (hmul : ∀ a b : G, χ (a * b) = χ a * χ b) (hnorm : ∀ a, ‖χ a‖ = 1)
    {n : ℕ} (hn : n ≠ 0) (hpow : ∀ x : G, (χ x) ^ n = 1) (x : G) : χ x = 1 := by
  classical
  have hTfin : {z : ℂ | z ^ n = 1}.Finite := by
    have hsub : {z : ℂ | z ^ n = 1} ⊆ ↑(Polynomial.nthRoots n (1 : ℂ)).toFinset := by
      intro z hz
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)]
      exact hz
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  have hTfin' : ({z : ℂ | z ^ n = 1} \ {1}).Finite := hTfin.subset Set.sdiff_subset
  set T : Finset ℂ := hTfin'.toFinset with hT
  have hTmem : ∀ z : ℂ, z ∈ T ↔ (z ^ n = 1 ∧ z ≠ 1) := by
    intro z
    rw [hT, Set.Finite.mem_toFinset]
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ T, δ ≤ ‖z - 1‖ := by
    rcases T.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz => by simp [h] at hz⟩
    · refine ⟨T.inf' h (fun z => ‖z - 1‖), ?_, fun z hz => Finset.inf'_le _ hz⟩
      rw [Finset.lt_inf'_iff]
      intro z hz
      have := (hTmem z).mp hz
      simpa [norm_pos_iff, sub_eq_zero] using this.2
  have hS : {y : G | χ y = 1} = χ ⁻¹' (Metric.ball (1 : ℂ) δ) := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_setOf_eq] at hy
      simp only [Set.mem_preimage, Metric.mem_ball, hy, dist_self]
      exact hδpos
    · intro hy
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
      by_contra hne
      have hmemT : χ y ∈ T := (hTmem _).mpr ⟨hpow y, hne⟩
      have := hδ _ hmemT
      linarith
  have hopen : IsOpen {y : G | χ y = 1} := by
    rw [hS]
    exact Metric.isOpen_ball.preimage hcont
  have hclosed : IsClosed {y : G | χ y = 1} := by
    have : {y : G | χ y = 1} = χ ⁻¹' {1} := rfl
    rw [this]
    exact (isClosed_singleton).preimage hcont
  have hne : ({y : G | χ y = 1}).Nonempty := ⟨1, char_one_eq_one hmul hnorm⟩
  have := (isClopen_iff.mp ⟨hclosed, hopen⟩)
  rcases this with h | h
  · exact absurd hne (by rw [h]; simp)
  · have : x ∈ {y : G | χ y = 1} := by rw [h]; trivial
    exact this

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] in
/-- A character is multiplicative on powers. -/
theorem char_pow {χ : G → ℂ} (hmul : ∀ a b : G, χ (a * b) = χ a * χ b)
    (hnorm : ∀ a, ‖χ a‖ = 1) (x : G) (m : ℕ) : χ (x ^ m) = (χ x) ^ m := by
  induction m with
  | zero => simp [char_one_eq_one hmul hnorm]
  | succ k ih => rw [pow_succ, hmul, ih, pow_succ]

/-! ## Divisibility of compact connected abelian groups -/

omit [MeasurableSpace G] [BorelSpace G] in
/-- **A compact connected abelian group is divisible.**  If the `n`-th power map were not
surjective, its closed image would admit a nontrivial character of the quotient; pulled back, that
character takes values in the `n`-th roots of unity, hence is trivial by connectedness. -/
theorem exists_pow_eq_of_connected [ConnectedSpace G] {n : ℕ} (hn : n ≠ 0) (g : G) :
    ∃ x : G, x ^ n = g := by
  classical
  by_contra hcon
  push Not at hcon
  set H : Subgroup G := (powMonoidHom n : G →* G).range with hH
  have hrange : (H : Set G) = Set.range (fun x : G => x ^ n) := rfl
  have hcompact : IsCompact (H : Set G) := by
    rw [hrange, ← Set.image_univ]
    exact isCompact_univ.image (continuous_pow n)
  haveI hHclosed : IsClosed (H : Set G) := hcompact.isClosed
  have hgH : g ∉ H := by
    intro hmem
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
    exact hcon x hx
  letI : MeasurableSpace (G ⧸ H) := borel (G ⧸ H)
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hne : (QuotientGroup.mk g : G ⧸ H) ≠ 1 := by
    intro h
    exact hgH ((QuotientGroup.eq_one_iff g).mp h)
  obtain ⟨ψ, hψc, hψm, hψn, hψg⟩ := exists_character_ne_one_mul (G := G ⧸ H) hne
  set χ : G → ℂ := fun x => ψ (QuotientGroup.mk x) with hχ
  have hχc : Continuous χ := hψc.comp continuous_quotient_mk'
  have hχm : ∀ a b : G, χ (a * b) = χ a * χ b := by
    intro a b
    simp only [hχ, QuotientGroup.mk_mul]
    exact hψm _ _
  have hχn : ∀ a : G, ‖χ a‖ = 1 := fun a => hψn _
  have hχpow : ∀ x : G, (χ x) ^ n = 1 := by
    intro x
    have hmem : x ^ n ∈ H := ⟨x, rfl⟩
    have h1 : (QuotientGroup.mk (x ^ n) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    have : χ (x ^ n) = 1 := by
      simp only [hχ, h1]
      exact char_one_eq_one hψm hψn
    rw [← char_pow hχm hχn x n]
    exact this
  exact hψg (character_eq_one_of_connected hχc hχm hχn hn hχpow g)

/-- A choice of `m`-th root in a compact connected abelian group. -/
noncomputable def natRoot [ConnectedSpace G] (a : G) (m : ℕ) : G :=
  if h : m = 0 then 1 else (exists_pow_eq_of_connected (n := m) h a).choose

omit [MeasurableSpace G] [BorelSpace G] in
theorem natRoot_pow [ConnectedSpace G] {m : ℕ} (hm : m ≠ 0) (a : G) :
    (natRoot a m) ^ m = a := by
  rw [natRoot, dif_neg hm]
  exact (exists_pow_eq_of_connected hm a).choose_spec

omit [MeasurableSpace G] [BorelSpace G] in
@[simp] theorem natRoot_zero [ConnectedSpace G] (a : G) : natRoot a 0 = 1 := by
  simp [natRoot]

/-- A compact connected abelian group is rootable by the integers. -/
noncomputable instance rootableByIntOfCompactConnected [ConnectedSpace G] : RootableBy G ℤ where
  root a n := if 0 ≤ n then natRoot a n.toNat else natRoot a⁻¹ (-n).toNat
  root_zero a := by simp
  root_cancel {n} a hn := by
    rcases le_or_gt 0 n with h | h
    · rw [if_pos h]
      have hm : n.toNat ≠ 0 := by omega
      have hcast : (natRoot a n.toNat) ^ n = (natRoot a n.toNat) ^ ((n.toNat : ℤ)) := by
        congr 1
        omega
      rw [hcast, zpow_natCast, natRoot_pow hm]
    · rw [if_neg (not_le.mpr h)]
      have hm : (-n).toNat ≠ 0 := by omega
      have hcast : (natRoot a⁻¹ (-n).toNat) ^ n
          = ((natRoot a⁻¹ (-n).toNat) ^ (((-n).toNat : ℤ)))⁻¹ := by
        rw [← zpow_neg]
        congr 1
        omega
      rw [hcast, zpow_natCast, natRoot_pow hm, inv_inv]

/-! ## Character kernels are null -/

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The image of a connected group under a nontrivial character is infinite. -/
theorem infinite_range_of_character [ConnectedSpace G] {χ : G → ℂ} (hcont : Continuous χ)
    {g : G} (hg : χ g ≠ 1) (h1 : χ 1 = 1) : (Set.range χ).Infinite := by
  have hconn : IsPreconnected (Set.range χ) := by
    rw [← Set.image_univ]
    exact (isPreconnected_univ).image χ hcont.continuousOn
  set d : ℝ := ‖χ g - 1‖ with hd
  have hdpos : 0 < d := by
    rw [hd, norm_pos_iff, sub_ne_zero]
    exact hg
  have himg : IsPreconnected ((fun z : ℂ => ‖z - 1‖) '' Set.range χ) :=
    hconn.image _ (by fun_prop)
  have h0mem : (0 : ℝ) ∈ (fun z : ℂ => ‖z - 1‖) '' Set.range χ :=
    ⟨χ 1, ⟨1, rfl⟩, by simp [h1]⟩
  have hdmem : d ∈ (fun z : ℂ => ‖z - 1‖) '' Set.range χ := ⟨χ g, ⟨g, rfl⟩, rfl⟩
  have hIcc : Set.Icc (0 : ℝ) d ⊆ (fun z : ℂ => ‖z - 1‖) '' Set.range χ :=
    himg.Icc_subset h0mem hdmem
  have hinf : ((fun z : ℂ => ‖z - 1‖) '' Set.range χ).Infinite :=
    Set.Infinite.mono hIcc (Set.Icc_infinite (by linarith))
  exact hinf.of_image _

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G] in
/-- **A nontrivial character of a compact connected abelian group has null kernel.**  The fibres of
the character are translates of the kernel, all of the same Haar measure, and the character has
infinitely many values. -/
theorem measure_character_fibre_eq_zero [ConnectedSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {χ : G → ℂ} (hcont : Continuous χ) (hmul : ∀ a b : G, χ (a * b) = χ a * χ b)
    (hnorm : ∀ a, ‖χ a‖ = 1) {g₀ : G} (hg₀ : χ g₀ ≠ 1) :
    μ (χ ⁻¹' {1}) = 0 := by
  classical
  by_contra hpos
  set c : ℝ≥0∞ := μ (χ ⁻¹' {1}) with hc
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hpos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 < (N : ℝ≥0∞) * c :=
    ENNReal.exists_nat_mul_gt (by simpa using hcpos.ne') ENNReal.one_ne_top
  have hinf := infinite_range_of_character hcont hg₀ (char_one_eq_one hmul hnorm)
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq N
  -- choose a preimage for each selected value
  have hchoice : ∀ z : ℂ, ∃ g : G, z ∈ T → χ g = z := by
    intro z
    by_cases hz : z ∈ T
    · obtain ⟨g, hg⟩ := hTsub hz
      exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun h => absurd h hz⟩
  choose pre hpre using hchoice
  set A : ℂ → Set G := fun z => χ ⁻¹' {z} with hA
  have hmeas : ∀ z : ℂ, MeasurableSet (A z) := fun z =>
    (hcont.measurable (measurableSet_singleton z))
  have hfibre : ∀ z ∈ T, μ (A z) = c := by
    intro z hz
    have hpz : χ (pre z) = z := hpre z hz
    have hzne : z ≠ 0 := by
      rw [← hpz]
      intro h0
      have hn := hnorm (pre z)
      rw [h0] at hn
      norm_num at hn
    have hset : A z = (fun x => pre z * x) '' (χ ⁻¹' {1}) := by
      ext x
      simp only [hA, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · intro hx
        refine ⟨(pre z)⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
        have hkey : χ ((pre z)⁻¹ * x) * χ (pre z) = z := by
          rw [← hmul, show (pre z)⁻¹ * x * pre z = x by
            rw [mul_comm ((pre z)⁻¹) x, mul_assoc, inv_mul_cancel, mul_one]]
          exact hx
        rw [hpz] at hkey
        field_simp at hkey
        exact hkey
      · rintro ⟨y, hy, rfl⟩
        rw [hmul, hy, hpz, mul_one]
    rw [hset, hc, Set.image_mul_left, measure_preimage_mul]
  have hdisj : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → Disjoint (A z) (A w) := by
    intro z _ w _ hzw
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact hzw (by rw [← (hx : χ x = z), (hx' : χ x = w)])
  have hsum : μ (⋃ z ∈ T, A z) = ∑ z ∈ T, μ (A z) := by
    rw [measure_biUnion_finset (fun z hz w hw hzw => hdisj z hz w hw hzw) (fun z _ => hmeas z)]
  have hbig : (N : ℝ≥0∞) * c ≤ 1 := by
    calc (N : ℝ≥0∞) * c = ∑ z ∈ T, μ (A z) := by
          rw [Finset.sum_congr rfl hfibre, Finset.sum_const, hTcard, nsmul_eq_mul]
      _ = μ (⋃ z ∈ T, A z) := hsum.symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact absurd hbig (not_le.mpr hN)

/-! ## Countability of the character group -/

/-- In a second-countable metric space every uniformly separated set is countable. -/
theorem countable_of_separated {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    {S : Set X} {δ : ℝ} (hδ : 0 < δ) (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    S.Countable := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense X
  have hchoice : ∀ x : X, ∃ d ∈ D, dist x d < δ / 3 := by
    intro x
    obtain ⟨d, hdD, hd⟩ := hDdense.exists_dist_lt (ε := δ / 3) x (by linarith)
    exact ⟨d, hdD, hd⟩
  choose f hfD hf using hchoice
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    by_contra hne
    have hsep := h x hx y hy hne
    have h1 := hf x
    have h2 := hf y
    rw [hxy] at h1
    have htri : dist x y ≤ dist x (f y) + dist (f y) y := dist_triangle _ _ _
    rw [dist_comm (f y) y] at htri
    linarith
  exact Set.MapsTo.countable_of_injOn (fun x _ => hfD x) hinj hDcount

/-- Continuous unitary characters, as a subset of the continuous functions. -/
def charSet (G : Type*) [TopologicalSpace G] [CommGroup G] : Set C(G, ℂ) :=
  {f | (∀ a b : G, f (a * b) = f a * f b) ∧ ∀ a, ‖f a‖ = 1}

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G] in
/-- The Haar integral of a nontrivial character vanishes. -/
theorem integral_character_eq_zero (μ : Measure G) [μ.IsMulLeftInvariant]
    {φ : G → ℂ} (hmul : ∀ a b : G, φ (a * b) = φ a * φ b) {g : G} (hg : φ g ≠ 1) :
    ∫ x, φ x ∂μ = 0 := by
  have h1 : ∫ x, φ (g * x) ∂μ = ∫ x, φ x ∂μ := integral_mul_left_eq_self φ g
  have h2 : ∫ x, φ (g * x) ∂μ = φ g * ∫ x, φ x ∂μ := by
    simp_rw [hmul]
    rw [integral_const_mul]
  rw [h2] at h1
  have h3 : (φ g - 1) * ∫ x, φ x ∂μ = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (by linear_combination h) hg
  · exact h

omit [T2Space G] [SecondCountableTopology G] in
/-- Distinct characters are orthonormal in `L²` of the Haar probability measure. -/
theorem dist_toLp_char (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {χ ψ : C(G, ℂ)} (hχ : χ ∈ charSet G) (hψ : ψ ∈ charSet G) (hne : χ ≠ ψ) :
    1 ≤ dist (ContinuousMap.toLp 2 μ ℂ χ) (ContinuousMap.toLp 2 μ ℂ ψ) := by
  classical
  set X := ContinuousMap.toLp (α := G) 2 μ ℂ χ with hX
  set Y := ContinuousMap.toLp (α := G) 2 μ ℂ ψ with hY
  have hae : ∀ f : C(G, ℂ), (fun a => (ContinuousMap.toLp (α := G) 2 μ ℂ f : G → ℂ) a)
      =ᵐ[μ] fun a => f a := fun f => ContinuousMap.coeFn_toLp μ f
  have hinner : ∀ f g : C(G, ℂ), (inner ℂ (ContinuousMap.toLp (α := G) 2 μ ℂ f)
      (ContinuousMap.toLp (α := G) 2 μ ℂ g) : ℂ)
      = ∫ a, (starRingEnd ℂ) (f a) * g a ∂μ := by
    intro f g
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hae f, hae g] with a h1 h2
    rw [RCLike.inner_apply, h1, h2]
    ring
  have hnormsq : ∀ f : C(G, ℂ), f ∈ charSet G →
      (inner ℂ (ContinuousMap.toLp (α := G) 2 μ ℂ f)
        (ContinuousMap.toLp (α := G) 2 μ ℂ f) : ℂ) = 1 := by
    intro f hf
    rw [hinner]
    have hone : ∀ a : G, (starRingEnd ℂ) (f a) * f a = 1 := by
      intro a
      have hc := Complex.mul_conj' (f a)
      rw [mul_comm, hc, hf.2 a]
      norm_num
    simp only [hone]
    simp
  have horth : (inner ℂ X Y : ℂ) = 0 := by
    rw [hX, hY, hinner]
    set φ : G → ℂ := fun a => (starRingEnd ℂ) (χ a) * ψ a with hφ
    have hφmul : ∀ a b : G, φ (a * b) = φ a * φ b := by
      intro a b
      simp only [hφ, hχ.1, hψ.1, map_mul]
      ring
    have hφne : ∃ g : G, φ g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext a
      have h := hcon a
      simp only [hφ] at h
      have hnz : χ a ≠ 0 := by
        intro h0
        have := hχ.2 a
        rw [h0] at this
        norm_num at this
      have hconj : (starRingEnd ℂ) (χ a) * χ a = 1 := by
        have hc := Complex.mul_conj' (χ a)
        rw [mul_comm, hc, hχ.2 a]
        norm_num
      have heq : (starRingEnd ℂ) (χ a) * ψ a = (starRingEnd ℂ) (χ a) * χ a := by
        rw [h, hconj]
      have hcnz : (starRingEnd ℂ) (χ a) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hconj
        exact zero_ne_one hconj
      exact (mul_left_cancel₀ hcnz heq).symm
    obtain ⟨g, hg⟩ := hφne
    exact integral_character_eq_zero μ hφmul hg
  have hXn : ‖X‖ = 1 := by
    have h := hnormsq χ hχ
    rw [← hX] at h
    have hr : ‖X‖ ^ 2 = 1 := by
      rw [← @inner_self_eq_norm_sq ℂ, h]
      simp
    nlinarith [norm_nonneg X]
  have hYn : ‖Y‖ = 1 := by
    have h := hnormsq ψ hψ
    rw [← hY] at h
    have hr : ‖Y‖ ^ 2 = 1 := by
      rw [← @inner_self_eq_norm_sq ℂ, h]
      simp
    nlinarith [norm_nonneg Y]
  have hsq : ‖X - Y‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, hXn, hYn, horth]
    norm_num
  have : (1:ℝ) ≤ ‖X - Y‖ := by nlinarith [norm_nonneg (X - Y)]
  rwa [dist_eq_norm]

include hBorelG hSecondG in
omit [T2Space G] in
/-- **The character group of a compact second-countable abelian group is countable.**  Distinct
characters are orthonormal in the separable Hilbert space `L²` of the Haar probability measure. -/
theorem countable_charSet (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    (charSet G).Countable := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hinj : Set.InjOn (ContinuousMap.toLp (α := G) 2 μ ℂ) (charSet G) := by
    intro x _ y _ h
    exact ContinuousMap.toLp_injective (μ := μ) (𝕜 := ℂ) (p := 2) h
  have hsep : ∀ x ∈ (ContinuousMap.toLp (α := G) 2 μ ℂ) '' charSet G,
      ∀ y ∈ (ContinuousMap.toLp (α := G) 2 μ ℂ) '' charSet G, x ≠ y → (1 : ℝ) ≤ dist x y := by
    rintro x ⟨χ, hχ, rfl⟩ y ⟨ψ, hψ, rfl⟩ hxy
    refine dist_toLp_char μ hχ hψ ?_
    intro h
    exact hxy (by rw [h])
  have himg : ((ContinuousMap.toLp (α := G) 2 μ ℂ) '' charSet G).Countable :=
    countable_of_separated one_pos hsep
  exact Set.MapsTo.countable_of_injOn (fun x hx => Set.mem_image_of_mem _ hx) hinj himg

/-! ## Dense generators -/

/-- The topological generators of a compact group. -/
def denseGenerators (G : Type*) [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] :
    Set G :=
  {α | (Subgroup.zpowers α).topologicalClosure = ⊤}

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- An element that does not generate densely is killed by a nontrivial character. -/
theorem exists_character_of_notMem_denseGenerators {α : G} (hα : α ∉ denseGenerators G) :
    ∃ χ : C(G, ℂ), χ ∈ charSet G ∧ (∃ g : G, χ g ≠ 1) ∧ χ α = 1 := by
  classical
  set H : Subgroup G := (Subgroup.zpowers α).topologicalClosure with hH
  haveI hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
  have hHne : H ≠ ⊤ := hα
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, g₀ ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hHne (Subgroup.eq_top_iff' H |>.mpr hcon)
  letI : MeasurableSpace (G ⧸ H) := borel (G ⧸ H)
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hne : (QuotientGroup.mk g₀ : G ⧸ H) ≠ 1 := by
    intro h
    exact hg₀ ((QuotientGroup.eq_one_iff g₀).mp h)
  obtain ⟨ψ, hψc, hψm, hψn, hψg⟩ := exists_character_ne_one_mul (G := G ⧸ H) hne
  refine ⟨⟨fun x => ψ (QuotientGroup.mk x), hψc.comp continuous_quotient_mk'⟩, ⟨?_, ?_⟩,
    ⟨g₀, hψg⟩, ?_⟩
  · intro a b
    show ψ (QuotientGroup.mk (a * b)) = ψ (QuotientGroup.mk a) * ψ (QuotientGroup.mk b)
    rw [QuotientGroup.mk_mul]
    exact hψm _ _
  · intro a
    exact hψn _
  · show ψ (QuotientGroup.mk α) = 1
    have hmem : α ∈ H := (Subgroup.le_topologicalClosure _) (Subgroup.mem_zpowers α)
    rw [(QuotientGroup.eq_one_iff α).mpr hmem]
    exact char_one_eq_one hψm hψn

omit [T2Space G] in
/-- **Almost every element of a compact connected second-countable abelian group is a topological
generator.** -/
theorem measure_compl_denseGenerators_eq_zero [ConnectedSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ (denseGenerators G)ᶜ = 0 := by
  classical
  set S : Set C(G, ℂ) := {χ | χ ∈ charSet G ∧ ∃ g : G, χ g ≠ 1} with hS
  have hScount : S.Countable := (countable_charSet μ).mono (fun x hx => hx.1)
  have hsub : (denseGenerators G)ᶜ ⊆ ⋃ χ ∈ S, (fun x : G => (χ : G → ℂ) x) ⁻¹' {1} := by
    intro α hα
    obtain ⟨χ, hχ, hnt, hone⟩ := exists_character_of_notMem_denseGenerators hα
    exact Set.mem_biUnion (show χ ∈ S from ⟨hχ, hnt⟩) hone
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hScount]
  intro χ hχ
  obtain ⟨g, hg⟩ := hχ.2
  exact measure_character_fibre_eq_zero μ χ.continuous hχ.1.1 hχ.1.2 hg

/-- **Minimax return lower mechanism.**  If the first `L` powers cannot cover a target of small
measure, some topological generator avoids the target through its first `L` powers. -/
theorem exists_denseGenerator_avoiding_of_measure_budget [ConnectedSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (B : Set G) (hB : MeasurableSet B) (L : ℕ) (hbudget : (L : ℝ≥0∞) * μ B < 1) :
    ∃ α ∈ denseGenerators G, ∀ n : ℕ, 0 < n → n ≤ L → α ^ n ∉ B :=
  exists_mem_avoids_first_powers_of_haar_budget μ B (denseGenerators G) hB
    (measure_compl_denseGenerators_eq_zero μ) L hbudget

end

end GaloisForLFunctions.HTGeometry
