import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction
import GaloisForLFunctions.RHTower.WeilFormConverseExplicitFormula
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# An integer counting function forces `Λ` and the Riemann hypothesis

Let `lam` be full-cone Weil-positive with boundary measure `μ = μ_lam`.  Suppose its counting
function is integer valued almost everywhere: there is a set `Y` of full Lebesgue measure with
`μ((a,b]) ∈ ℕ` for all `a < b` in `Y`.  Suppose also that `μ` has no mass on `(−1, 1)`.

**Theorem** (`vonMangoldt_and_riemannHypothesis_of_integer_counting`).  Then `lam(n) = Λ(n)` for
every `n ≥ 2`, and the Riemann hypothesis holds.

Along the critical line the cumulative boundary mass `μ((0,t])` is `1/π` times the argument of the
completed exponential `s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)`.  The hypothesis therefore says
that this completed exponential has constant phase modulo `π` at almost every point of the line.
No analytic continuation across the line and no regularity of the boundary values are assumed.

**Proof.**
* Integer counting on a dense set isolates every point.  Each `x` has an open interval `I ∋ x`
  with `μ(I ∖ {x}) = 0` and `μ{x} ∈ ℕ` (`exists_isolating_interval`).  Lindelöf's theorem then
  makes the non-atoms `μ`-null and the atoms countable (`atoms_countable_and_compl_null`), so `μ`
  is a countable sum of integer point masses.
* The Weil continuation satisfies `Φ(s̄) = conj Φ(s)` on `Re s > 1/2`.  This holds on `Re s > 1`,
  where `Φ` is the explicit Weil function with real coefficients, and extends by the identity
  theorem.  Atom extraction then gives `μ{−a} = μ{a}`.
* Hence `W_lam(f ⋆ f̃) = ∫ |f̂|² dμ = Σ_j m_j (|f̂(t_j)|² + |f̂(−t_j)|²)`, with integers `m_j` and
  ordinates `t_j ≥ 1`.  The converse explicit formula (`converse_explicit_formula`) concludes.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## Integer counting functions on the line -/

/-- A set of full Lebesgue measure meets every nonempty open interval. -/
theorem exists_mem_Ioo_of_compl_null {Y : Set ℝ} (hY : volume Yᶜ = 0) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Y, a < y ∧ y < b := by
  by_contra h
  have hsub : Ioo a b ⊆ Yᶜ := fun y hy hyY => h ⟨y, hyY, hy.1, hy.2⟩
  have h0 := measure_mono_null hsub hY
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- The shrinking intervals `(x − 1/(n+1), x + 1/(n+1))` decrease to `{x}`. -/
theorem iInter_Ioo_shrink (x : ℝ) :
    ⋂ n : ℕ, Ioo (x - 1 / ((n : ℝ) + 1)) (x + 1 / ((n : ℝ) + 1)) = {x} := by
  ext y
  simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    obtain ⟨h1, h2⟩ := h n
    have : |y - x| < 1 / ((n : ℝ) + 1) := by rw [abs_lt]; constructor <;> linarith
    linarith
  · rintro rfl n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    constructor <;> linarith

theorem antitone_Ioo_shrink (x : ℝ) :
    Antitone fun n : ℕ => Ioo (x - 1 / ((n : ℝ) + 1)) (x + 1 / ((n : ℝ) + 1)) := by
  intro m n hmn
  have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  exact Ioo_subset_Ioo (by linarith) (by linarith)

/-- Two natural numbers in a half-open interval of length `1/2` coincide. -/
theorem nat_eq_of_mem_half_interval {m : ℝ} {k l : ℕ} (hk1 : m ≤ k) (hk2 : (k : ℝ) < m + 1 / 2)
    (hl1 : m ≤ l) (hl2 : (l : ℝ) < m + 1 / 2) : k = l := by
  have h1 : (k : ℝ) < l + 1 := by linarith
  have h2 : (l : ℝ) < k + 1 := by linarith
  have h1' : k < l + 1 := by exact_mod_cast h1
  have h2' : l < k + 1 := by exact_mod_cast h2
  omega

/-- **Isolation.**  If `μ` is finite on bounded open intervals and `μ((a,b]) ∈ ℕ` for all `a < b`
in a set of full Lebesgue measure, then every point `x` has an open interval around it on which `μ`
lives only at `x`, and `μ{x}` is a natural number. -/
theorem exists_isolating_interval {μ : Measure ℝ} (hfin : ∀ a b : ℝ, μ (Ioo a b) ≠ ∞)
    {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b → ∃ k : ℕ, μ (Ioc a b) = k) (x : ℝ) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ μ (Ioo a b \ {x}) = 0 ∧ ∃ k : ℕ, μ {x} = k := by
  set s : ℕ → Set ℝ := fun n => Ioo (x - 1 / ((n : ℝ) + 1)) (x + 1 / ((n : ℝ) + 1)) with hs
  have htend : Tendsto (fun n => μ (s n)) atTop (𝓝 (μ {x})) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := s)
      (fun n => measurableSet_Ioo.nullMeasurableSet) (antitone_Ioo_shrink x) ⟨0, hfin _ _⟩
    rwa [show ⋂ n, s n = {x} from iInter_Ioo_shrink x] at h
  have hx_mem : ∀ n, x ∈ s n := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hs, mem_Ioo]; constructor <;> linarith
  have hxfin : μ {x} ≠ ∞ :=
    ne_top_of_le_ne_top (hfin _ _) (measure_mono (singleton_subset_iff.mpr (hx_mem 0)))
  -- an integer point mass in every shrinking interval
  have hpick : ∀ n : ℕ, ∃ a b : ℝ, ∃ k : ℕ, x - 1 / ((n : ℝ) + 1) < a ∧ a < x ∧ x < b ∧
      b < x + 1 / ((n : ℝ) + 1) ∧ μ (Ioc a b) = k := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨a, haY, ha1, ha2⟩ := exists_mem_Ioo_of_compl_null hY (show x - 1 / ((n : ℝ) + 1) < x by
      linarith)
    obtain ⟨b, hbY, hb1, hb2⟩ := exists_mem_Ioo_of_compl_null hY (show x < x + 1 / ((n : ℝ) + 1) by
      linarith)
    obtain ⟨k, hk⟩ := hcount a haY b hbY (by linarith)
    exact ⟨a, b, k, ha1, ha2, hb1, hb2, hk⟩
  choose A B K hA1 hA2 hB1 hB2 hK using hpick
  have hIoc_sub : ∀ n, Ioc (A n) (B n) ⊆ s n := fun n y hy => by
    simp only [hs, mem_Ioo]; exact ⟨by linarith [hy.1, hA1 n], by linarith [hy.2, hB2 n]⟩
  have hx_Ioc : ∀ n, x ∈ Ioc (A n) (B n) := fun n => ⟨hA2 n, (hB1 n).le⟩
  have hlow : ∀ n, μ {x} ≤ K n := fun n => by
    rw [← hK n]; exact measure_mono (singleton_subset_iff.mpr (hx_Ioc n))
  have hup : ∀ n, (K n : ℝ≥0∞) ≤ μ (s n) := fun n => by
    rw [← hK n]; exact measure_mono (hIoc_sub n)
  -- eventually the shrinking masses are below `μ{x} + 1/2`
  have hlt : μ {x} < μ {x} + (1 / 2 : ℝ≥0∞) := ENNReal.lt_add_right hxfin (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hlt))
  set m := (μ {x}).toReal with hm
  have hK_real : ∀ n, N ≤ n → m ≤ K n ∧ (K n : ℝ) < m + 1 / 2 := by
    intro n hn
    have h1 := hlow n
    have h2 : (K n : ℝ≥0∞) < μ {x} + 1 / 2 := lt_of_le_of_lt (hup n) (hN n hn)
    have hfin' : μ {x} + (1 / 2 : ℝ≥0∞) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hxfin, by norm_num⟩
    constructor
    · have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h1
      simpa [hm] using this
    · have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top _) hfin').mpr h2
      rw [ENNReal.toReal_add hxfin (by norm_num)] at this
      simpa [hm] using this
  have hconst : ∀ n, N ≤ n → K n = K N := fun n hn =>
    nat_eq_of_mem_half_interval (hK_real n hn).1 (hK_real n hn).2 (hK_real N le_rfl).1
      (hK_real N le_rfl).2
  -- the integer value equals the point mass
  have hKle : (K N : ℝ≥0∞) ≤ μ {x} := by
    refine ge_of_tendsto' htend fun n => ?_
    rcases le_total N n with hn | hn
    · rw [← hconst n hn]; exact hup n
    · exact (hup N).trans (measure_mono (antitone_Ioo_shrink x hn))
  have hxK : μ {x} = K N := le_antisymm (hlow N) hKle
  refine ⟨A N, B N, hA2 N, hB1 N, ?_, K N, hxK⟩
  have hIocfin : μ (Ioc (A N) (B N)) ≠ ∞ := by rw [hK N]; exact ENNReal.natCast_ne_top _
  have hdiff : μ (Ioc (A N) (B N) \ {x}) = 0 := by
    rw [measure_sdiff (singleton_subset_iff.mpr (hx_Ioc N)) (measurableSet_singleton x).nullMeasurableSet
      hxfin, hK N, hxK, tsub_self]
  exact measure_mono_null (sdiff_subset_sdiff_left Ioo_subset_Ioc_self) hdiff

/-- **Integer counting forces an atomic measure.**  Under the hypotheses of
`exists_isolating_interval`, the atoms of `μ` form a countable set and their complement is
`μ`-null. -/
theorem atoms_countable_and_compl_null {μ : Measure ℝ} (hfin : ∀ a b : ℝ, μ (Ioo a b) ≠ ∞)
    {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b → ∃ k : ℕ, μ (Ioc a b) = k) :
    {x : ℝ | μ {x} ≠ 0}.Countable ∧ μ {x : ℝ | μ {x} ≠ 0}ᶜ = 0 := by
  choose a b hax hxb hnull k _ using exists_isolating_interval hfin hY hcount
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x => Ioo (a x) (b x)) fun _ => isOpen_Ioo
  have hcover : ∀ y : ℝ, ∃ x ∈ T, y ∈ Ioo (a x) (b x) := by
    intro y
    have hy : y ∈ ⋃ x, Ioo (a x) (b x) := mem_iUnion.mpr ⟨y, hax y, hxb y⟩
    rw [← hTU] at hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp hy
    exact ⟨x, hxT, hyx⟩
  set S := {x : ℝ | μ {x} ≠ 0} with hS
  have hloc : ∀ x, ∀ y ∈ Ioo (a x) (b x), y ∈ S → y = x := by
    intro x y hy hyS
    by_contra hne
    exact hyS (measure_mono_null
      (singleton_subset_iff.mpr (show y ∈ Ioo (a x) (b x) \ {x} from ⟨hy, hne⟩)) (hnull x))
  constructor
  · refine hTc.mono fun y hyS => ?_
    obtain ⟨x, hxT, hyx⟩ := hcover y
    rw [hloc x y hyx hyS]
    exact hxT
  · have hsub : Sᶜ ⊆ ⋃ x ∈ T, ((Ioo (a x) (b x) \ {x}) ∪ ({x} ∩ Sᶜ)) := by
      intro y hy
      obtain ⟨x, hxT, hyx⟩ := hcover y
      refine mem_iUnion₂.mpr ⟨x, hxT, ?_⟩
      by_cases hyx' : y = x
      · exact Or.inr ⟨mem_singleton_iff.mpr hyx', hy⟩
      · exact Or.inl ⟨hyx, hyx'⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).mpr fun x _ => ?_)
    refine measure_union_null (hnull x) ?_
    by_cases hxS : x ∈ S
    · rw [show ({x} : Set ℝ) ∩ Sᶜ = ∅ from by
        ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false,
          iff_false, not_and, not_not]; rintro rfl; exact hxS]
      exact measure_empty
    · have hx0 : μ {x} = 0 := by simpa [hS] using hxS
      exact measure_mono_null inter_subset_left hx0

/-! ## Symmetry of the atoms -/

theorem lamC_conj (lam : ℕ → ℝ) (n : ℕ) : conj (lamC lam n) = lamC lam n := by
  simp [lamC]

theorem natCast_cpow_conj' (n : ℕ) (s : ℂ) : conj ((n : ℂ) ^ s) = (n : ℂ) ^ conj s := by
  have h := Complex.conj_cpow (n : ℂ) s (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast] at h
  rw [h, Complex.conj_conj]

theorem LSeries_lamC_conj (lam : ℕ → ℝ) (s : ℂ) :
    LSeries (lamC lam) (conj s) = conj (LSeries (lamC lam) s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, if_false, map_div₀, lamC_conj, natCast_cpow_conj']

/-- The Weil function has real coefficients: `Φ(s̄) = conj Φ(s)`. -/
theorem weilFunction_conj (lam : ℕ → ℝ) (s : ℂ) :
    weilFunction lam (conj s) = conj (weilFunction lam s) := by
  have hd : Complex.digamma (conj s / 2) = conj (Complex.digamma (s / 2)) := by
    rw [← ReflectedDigammaAnomaly.digamma_conj, map_div₀, map_ofNat]
  simp only [weilFunction, map_sub, map_add, map_div₀, map_one, Complex.conj_ofReal, map_ofNat,
    LSeries_lamC_conj, hd]

/-- The Weil continuation satisfies `Φ(s̄) = conj Φ(s)` on `Re s > 1/2`. -/
theorem weilContinuation_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 / 2 < s.re) : weilContinuation hW (conj s) = conj (weilContinuation hW s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set f := weilContinuation hW with hf
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) with hg
  have hfd : DifferentiableOn ℂ f U := differentiableOn_weilContinuation hW
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : conj z ∈ U := by simpa [hU] using hz
    have h := ((hfd (conj z) hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  have heq : f =ᶠ[𝓝 2] g := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    simp only [hg, Function.comp_apply, hf]
    rw [weilContinuation_eq hW hz, weilContinuation_eq hW hz', weilFunction_conj,
      Complex.conj_conj]
  have hEq := (hfd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hcs : conj s ∈ U := by simpa [hU] using hs
  have := hEq hcs
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- The boundary measure is finite on bounded open intervals. -/
theorem boundaryMeasure_Ioo_ne_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ) :
    boundaryMeasure hW (Ioo a b) ≠ ∞ := by
  set μ := boundaryMeasure hW
  set R : ℝ := max |a| |b| with hR
  have hint := integrable_inv_one_add_sq_sub hW 0
  set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / (1 + (r - 0) ^ 2)) with hgdef
  have hgfin : ∫⁻ r, g r ∂μ < ∞ := by
    have h := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by positivity)] at h
    exact h
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + R ^ 2)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsub : Ioo a b ⊆ {r | c ≤ g r} := by
    intro r hr
    simp only [mem_setOf_eq, hc, hgdef, sub_zero]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (by positivity)
    have hr2 : r ^ 2 ≤ R ^ 2 := by
      have h1 : |r| ≤ R := by
        rw [abs_le]
        constructor
        · have := neg_abs_le a; have := le_max_left |a| |b|; linarith [hr.1]
        · have := le_abs_self b; have := le_max_right |a| |b|; linarith [hr.2]
      have h0 : 0 ≤ |r| := abs_nonneg r
      calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
        _ ≤ R ^ 2 := pow_le_pow_left₀ h0 h1 2
    linarith
  have hmeas : AEMeasurable g μ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun r : ℝ => 1 / (1 + (r - 0) ^ 2))).aemeasurable
  have hle := mul_meas_ge_le_lintegral₀ hmeas c
  have hmono : c * μ (Ioo a b) ≤ c * μ {r | c ≤ g r} := by gcongr
  have hfin2 : c * μ (Ioo a b) < ∞ := lt_of_le_of_lt (hmono.trans hle) hgfin
  intro htop
  rw [htop, ENNReal.mul_top hc0] at hfin2
  exact lt_irrefl _ hfin2

/-- **Symmetry of the atoms.**  `μ_lam{−a} = μ_lam{a}`. -/
theorem boundaryMeasure_singleton_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a : ℝ) :
    boundaryMeasure hW {-a} = boundaryMeasure hW {a} := by
  have h1 := tendsto_mul_re_weilContinuation_atom hW a
  have h2 := tendsto_mul_re_weilContinuation_atom hW (-a)
  have hfun : ∀ b : ℝ, 0 < b →
      b * (weilContinuation hW (((1 / 2 + b : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I)).re =
        b * (weilContinuation hW (((1 / 2 + b : ℝ) : ℂ) + (a : ℂ) * I)).re := by
    intro b hb
    have hre : 1 / 2 < ((((1 / 2 + b : ℝ) : ℂ) + (a : ℂ) * I)).re := by simp; linarith
    have hc : (((1 / 2 + b : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I) =
        conj (((1 / 2 + b : ℝ) : ℂ) + (a : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hc, weilContinuation_conj hW hre, Complex.conj_re]
  have h2' : Tendsto (fun b : ℝ => b * (weilContinuation hW (((1 / 2 + b : ℝ) : ℂ) +
      (a : ℂ) * I)).re) (𝓝[>] 0) (𝓝 ((boundaryMeasure hW).real {-a})) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact hfun b hb
  have hreal := tendsto_nhds_unique h2' h1
  have hfa : boundaryMeasure hW {a} ≠ ∞ :=
    ne_top_of_le_ne_top (boundaryMeasure_Ioo_ne_top hW (a - 1) (a + 1))
      (measure_mono (singleton_subset_iff.mpr ⟨by linarith, by linarith⟩))
  have hfna : boundaryMeasure hW {-a} ≠ ∞ :=
    ne_top_of_le_ne_top (boundaryMeasure_Ioo_ne_top hW (-a - 1) (-a + 1))
      (measure_mono (singleton_subset_iff.mpr ⟨by linarith, by linarith⟩))
  rw [Measure.real, Measure.real] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hfna hfa).mp hreal

/-! ## The atomic representation of the Weil form -/

theorem lintegral_inv_one_add_sq_lt_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∫⁻ r, ENNReal.ofReal (1 / (1 + r ^ 2)) ∂boundaryMeasure hW < ∞ := by
  have h := (integrable_inv_one_add_sq_sub hW 0).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by positivity)] at h
  simpa using h

/-- Reindexing a countable set of reals along its encoding. -/
theorem tsum_decode₂_eq {P : Set ℝ} [Encodable P] (k : P → ℕ) (G : ℝ → ℝ) :
    ∑' j : ℕ, (((Encodable.decode₂ P j).elim 0 fun x => k x : ℕ) : ℝ) *
        G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ)) =
      ∑' x : P, (k x : ℝ) * G x := by
  set F : ℕ → ℝ := fun j => (((Encodable.decode₂ P j).elim 0 fun x => k x : ℕ) : ℝ) *
    G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ)) with hF
  have hsupp : Function.support F ⊆ range (Encodable.encode : P → ℕ) := by
    intro j hj
    rcases hd : Encodable.decode₂ P j with _ | x
    · exfalso; apply hj; simp [hF, hd]
    · exact ⟨x, Encodable.mem_decode₂.mp hd⟩
  have h := Function.Injective.tsum_eq (Encodable.encode_injective (α := P)) hsupp
  rw [← h]
  congr 1
  funext x
  simp [hF]

theorem summable_decode₂_iff {P : Set ℝ} [Encodable P] (k : P → ℕ) (G : ℝ → ℝ) :
    Summable (fun j : ℕ => (((Encodable.decode₂ P j).elim 0 fun x => k x : ℕ) : ℝ) *
        G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ))) ↔
      Summable fun x : P => (k x : ℝ) * G x := by
  set F : ℕ → ℝ := fun j => (((Encodable.decode₂ P j).elim 0 fun x => k x : ℕ) : ℝ) *
    G ((Encodable.decode₂ P j).elim 1 fun x => (x : ℝ)) with hF
  have hoff : ∀ j ∉ range (Encodable.encode : P → ℕ), F j = 0 := by
    intro j hj
    rcases hd : Encodable.decode₂ P j with _ | x
    · simp [hF, hd]
    · exact absurd ⟨x, Encodable.mem_decode₂.mp hd⟩ hj
  have h := Function.Injective.summable_iff (Encodable.encode_injective (α := P)) hoff
  have hcomp : F ∘ (Encodable.encode : P → ℕ) = fun x : P => (k x : ℝ) * G x := by
    funext x; simp [hF]
  rw [← hcomp]
  exact h.symm

/-- **An integer counting function forces `Λ` and the Riemann hypothesis.**  Let `lam` be
full-cone Weil-positive.  Suppose the boundary measure `μ_lam` has integer mass on `(a, b]` for all
`a < b` in a set of full Lebesgue measure, and no mass on `(−1, 1)`.  Then `lam(n) = Λ(n)` for
every `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem vonMangoldt_and_riemannHypothesis_of_integer_counting {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b → ∃ k : ℕ, boundaryMeasure hW (Ioc a b) = k)
    (hgap : boundaryMeasure hW (Ioo (-1) 1) = 0) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set μ := boundaryMeasure hW with hμ
  have hfin := boundaryMeasure_Ioo_ne_top hW
  obtain ⟨hSc, hSnull⟩ := atoms_countable_and_compl_null hfin hY hcount
  set S := {x : ℝ | μ {x} ≠ 0} with hS
  have hint : ∀ x, ∃ k : ℕ, μ {x} = k := fun x => by
    obtain ⟨_, _, _, _, _, hk⟩ := exists_isolating_interval hfin hY hcount x
    exact hk
  choose kk hkk using hint
  have hS1 : ∀ x ∈ S, 1 ≤ |x| := by
    intro x hx
    by_contra h
    have h' : |x| < 1 := lt_of_not_ge h
    have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp h'
    exact hx (measure_mono_null (singleton_subset_iff.mpr hmem) hgap)
  set P := {x : ℝ | μ {x} ≠ 0 ∧ 0 < x} with hP
  set N := {x : ℝ | μ {x} ≠ 0 ∧ x < 0} with hN
  have hPc : P.Countable := hSc.mono fun x hx => hx.1
  have hP1 : ∀ x ∈ P, 1 ≤ x := by
    intro x hx
    have h := hS1 x hx.1
    rwa [abs_of_pos hx.2] at h
  have hSPN : S = P ∪ N := by
    ext x
    simp only [hS, hP, hN, mem_setOf_eq, mem_union]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr ⟨hx, h⟩
      · exfalso; have := hS1 x hx; rw [h, abs_zero] at this; linarith
      · exact Or.inl ⟨hx, h⟩
    · rintro (h | h) <;> exact h.1
  have hPN : Disjoint P N := by
    rw [Set.disjoint_left]
    intro x hxP hxN
    linarith [hxP.2, hxN.2]
  have hneg : ∀ x : ℝ, x ∈ P ↔ (Equiv.neg ℝ) x ∈ N := by
    intro x
    have hsym : μ {-x} = μ {x} := boundaryMeasure_singleton_neg hW x
    simp only [hP, hN, mem_setOf_eq, Equiv.neg_apply, hsym, neg_lt_zero]
  -- the lintegral against `μ` is a sum over the positive atoms
  have hrepr : ∀ g : ℝ → ℝ≥0∞,
      ∫⁻ r, g r ∂μ = ∑' x : P, (g x + g (-x)) * (kk x : ℝ≥0∞) := by
    intro g
    have hae : ∀ᵐ r ∂μ, r ∈ S := by
      rw [ae_iff]; exact hSnull
    rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_countable g hSc]
    set F : ℝ → ℝ≥0∞ := fun y => g y * μ {y} with hF
    have h1 : ∑' y : S, g y * μ {(y : ℝ)} = ∑' y : P, F y + ∑' y : N, F y := by
      rw [show (∑' y : S, g y * μ {(y : ℝ)}) = ∑' y : S, F y from rfl, tsum_subtype,
        tsum_subtype, tsum_subtype, hSPN, indicator_union_of_disjoint hPN, ENNReal.tsum_add]
    have h2 : ∑' y : N, F y = ∑' x : P, F (-x) := by
      rw [← Equiv.tsum_eq (Equiv.subtypeEquiv (Equiv.neg ℝ) hneg) fun y : N => F y]
      rfl
    rw [h1, h2, ← ENNReal.tsum_add]
    congr 1
    funext x
    have hsym : μ {-(x : ℝ)} = μ {(x : ℝ)} := boundaryMeasure_singleton_neg hW x
    show g x * μ {(x : ℝ)} + g (-x) * μ {-(x : ℝ)} = _
    rw [hsym, hkk, add_mul]
  -- the ordinates and masses
  haveI : Encodable P := hPc.toEncodable
  set t : ℕ → ℝ := fun j => (Encodable.decode₂ P j).elim 1 fun x => (x : ℝ) with ht
  set m : ℕ → ℕ := fun j => (Encodable.decode₂ P j).elim 0 fun x => kk x with hm
  have hone : ∀ j, 1 ≤ t j := by
    intro j
    simp only [ht]
    rcases Encodable.decode₂ P j with _ | x
    · simp
    · exact hP1 x x.2
  have hsum : Summable fun j => (m j : ℝ) / t j ^ 2 := by
    have hconv : (fun j => (m j : ℝ) / t j ^ 2) =
        fun j => (m j : ℝ) * (fun r : ℝ => 1 / r ^ 2) (t j) := by
      funext j; simp [div_eq_mul_inv]
    rw [hconv]
    refine (summable_decode₂_iff (fun x : P => kk x) (fun r : ℝ => 1 / r ^ 2)).mpr ?_
    -- compare with `1/(1+x²)`
    set g : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / (1 + r ^ 2)) with hg
    have hfinite : ∑' x : P, (g x + g (-x)) * (kk x : ℝ≥0∞) ≠ ∞ := by
      rw [← hrepr g]; exact (lintegral_inv_one_add_sq_lt_top hW).ne
    have hsumE := ENNReal.summable_toReal hfinite
    have hterm : ∀ x : P, ((g x + g (-x)) * (kk x : ℝ≥0∞)).toReal =
        (kk x : ℝ) * (2 * (1 / (1 + (x : ℝ) ^ 2))) := by
      intro x
      simp only [hg, neg_sq]
      rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast]
      ring
    simp_rw [hterm] at hsumE
    refine hsumE.of_nonneg_of_le (fun x => by positivity) fun x => ?_
    have hx1 := hP1 x x.2
    have hk0 : (0 : ℝ) ≤ kk x := Nat.cast_nonneg _
    apply mul_le_mul_of_nonneg_left _ hk0
    show 1 / (x : ℝ) ^ 2 ≤ 2 * (1 / (1 + (x : ℝ) ^ 2))
    have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hform : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      weilFullFunctional lam (Zeta23.EF.weilTest f f) = (zeroSumForm m t f : ℂ) := by
    intro f hf hfc
    rw [(weilFullFunctional_weilTest_eq_lintegral hW hf hfc).2, ← hμ,
      hrepr fun r => (specDensity f r : ℝ≥0∞)]
    congr 1
    rw [ENNReal.tsum_toReal_eq fun x => ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) (ENNReal.natCast_ne_top _)]
    have hterm : ∀ x : P, (((specDensity f x : ℝ≥0∞) + (specDensity f (-x) : ℝ≥0∞)) *
        (kk x : ℝ≥0∞)).toReal =
        (kk x : ℝ) * (fun r : ℝ => ‖paperFT f r‖ ^ 2 + ‖paperFT f ((-r : ℝ) : ℂ)‖ ^ 2) x := by
      intro x
      rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top,
        ENNReal.toReal_natCast]
      simp [specDensity, mul_comm]
    simp_rw [hterm]
    rw [zeroSumForm]
    exact (tsum_decode₂_eq (fun x : P => kk x)
      (fun r : ℝ => ‖paperFT f r‖ ^ 2 + ‖paperFT f ((-r : ℝ) : ℂ)‖ ^ 2)).symm
  exact converse_explicit_formula hone hsum hform

end RHTower.WeilSpectral

end
