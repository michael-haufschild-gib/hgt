import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.JacobiThetaDefectMeromorphicOrder

/-!
# Constant-coefficient differential operators preserve meromorphic simple poles

The `j`th derivative of a meromorphic simple pole has exact order `-(j+1)`.  Consequently a
nonzero polynomial in the derivation has exact pole order `-(degree+1)`: its highest derivative is
strictly more singular than every lower term and cannot cancel.  The final theorem applies this to
the translated theta defect and proves exact preservation of its two pole lattices.
-/

open Complex Set Filter Finset
open scoped Topology

namespace GaloisForLFunctions

noncomputable section

/-- Every derivative of a meromorphic simple pole has a nonzero normalized leading limit. -/
theorem exists_tendsto_iteratedDeriv_of_meromorphic_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) (j : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun z : ℂ => (z - p) ^ (j + 1) * iteratedDeriv j f z)
        (𝓝[≠] p) (𝓝 c) := by
  obtain ⟨g, hg, hgne, hfacptd⟩ := (meromorphicOrderAt_eq_int_iff hf).mp horder
  have hfac' : f =ᶠ[𝓝[≠] p] fun z => (z - p)⁻¹ * g z := by
    filter_upwards [hfacptd] with z hz
    rw [hz]
    simp [zpow_neg, zpow_one]
  have hcomb : {z : ℂ | f z = (z - p)⁻¹ * g z ∧ g z ≠ 0 ∧
      ∀ m : ℕ, ContDiffAt ℂ m g z} ∈ 𝓝[≠] p := by
    filter_upwards [hfac', nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgne),
      nhdsWithin_le_nhds hg.eventually_analyticAt] with z h1 h2 h3
    exact ⟨h1, h2, fun m => h3.contDiffAt⟩
  rw [Metric.mem_nhdsWithin_iff] at hcomb
  obtain ⟨ε, hε, hsub⟩ := hcomb
  let U := Metric.ball p ε \ {p}
  have hUsub : U ⊆ {z : ℂ | f z = (z - p)⁻¹ * g z ∧ g z ≠ 0 ∧
      ∀ m : ℕ, ContDiffAt ℂ m g z} := by
    intro z hz
    apply hsub
    refine ⟨hz.1, ?_⟩
    simpa [U] using hz.2
  have hUnhds : ∀ᶠ z in 𝓝[≠] p, z ∈ U := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds p hε),
      self_mem_nhdsWithin] with z hb hne
    exact ⟨hb, hne⟩
  have hlimit := iteratedDeriv_residue_of_factor_add f g (-p) U
    (fun z hz hzp => hz.2 (by
      simp only [mem_singleton_iff]
      linear_combination hzp))
    (by simpa using hUnhds)
    (fun z hz m => (hUsub hz).2.2 m)
    (by simpa using fun m => hg.contDiffAt)
    (fun z hz => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hz) (fun t ht => ?_)
      show f t = g t * (t + -p)⁻¹
      rw [(hUsub ht).1]
      ring)
    j
  let c : ℂ := g p * ((-1)^j * (j.factorial : ℂ))
  refine ⟨c, mul_ne_zero hgne (mul_ne_zero (pow_ne_zero j (by norm_num)) ?_), ?_⟩
  · exact_mod_cast Nat.factorial_ne_zero j
  simpa [c, sub_eq_add_neg] using hlimit

/-- A nonzero normalized `k`th-order pole limit determines meromorphic order `-k`. -/
theorem meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul
    {f : ℂ → ℂ} {p c : ℂ} (k : ℕ) (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (hlim : Tendsto (fun z : ℂ => (z - p) ^ k * f z) (𝓝[≠] p) (𝓝 c)) :
    meromorphicOrderAt f p = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
  have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ k) p := by fun_prop
  have hprod : MeromorphicAt (fun z : ℂ => (z - p) ^ k * f z) p := hpow.mul hf
  have hzero : meromorphicOrderAt (fun z : ℂ => (z - p) ^ k * f z) p = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).1 ⟨c, hc, hlim⟩
  change meromorphicOrderAt ((fun z : ℂ => (z - p) ^ k) * f) p = 0 at hzero
  rw [meromorphicOrderAt_mul hpow hf] at hzero
  have hpowOrder : meromorphicOrderAt (fun z : ℂ => (z - p) ^ k) p =
      ((k : ℤ) : WithTop ℤ) := by
    simpa only using! (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
  rw [hpowOrder] at hzero
  have hfinite : meromorphicOrderAt f p ≠ ⊤ := by
    intro htop
    rw [htop] at hzero
    simp at hzero
  lift meromorphicOrderAt f p to ℤ using hfinite with n hn
  have hzero' : (k : ℤ) + n = 0 := by exact_mod_cast hzero
  have hnneg : n = -(k : ℤ) := by omega
  simp [hnneg]

/-- A finite normalized pole limit detects exact meromorphic order precisely when its value is
nonzero. -/
theorem meromorphicOrderAt_eq_neg_nat_iff_limit_ne_zero
    {f : ℂ → ℂ} {p c : ℂ} (k : ℕ) (hf : MeromorphicAt f p)
    (hlim : Tendsto (fun z : ℂ => (z - p) ^ k * f z) (𝓝[≠] p) (𝓝 c)) :
    meromorphicOrderAt f p = ((-(k : ℤ) : ℤ) : WithTop ℤ) ↔ c ≠ 0 := by
  constructor
  · intro horder hc
    subst c
    have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ k) p := by fun_prop
    have hprod : MeromorphicAt (fun z : ℂ => (z - p) ^ k * f z) p := hpow.mul hf
    have hpowOrder : meromorphicOrderAt (fun z : ℂ => (z - p) ^ k) p =
        ((k : ℤ) : WithTop ℤ) := by
      simpa only using!
        (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
    have hprodOrder :
        meromorphicOrderAt (fun z : ℂ => (z - p) ^ k * f z) p = 0 := by
      change meromorphicOrderAt ((fun z : ℂ => (z - p) ^ k) * f) p = 0
      rw [meromorphicOrderAt_mul hpow hf, hpowOrder, horder]
      norm_num
    obtain ⟨d, hd, hdlim⟩ :=
      tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hprod hprodOrder
    exact hd (tendsto_nhds_unique hdlim hlim)
  · intro hc
    exact meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul k hf hc hlim

/-- A vanishing normalized `k`th-pole limit forces strict improvement over order `-k`. -/
theorem neg_nat_lt_meromorphicOrderAt_of_tendsto_pow_mul_zero
    {f : ℂ → ℂ} {p : ℂ} (k : ℕ) (hf : MeromorphicAt f p)
    (hlim : Tendsto (fun z : ℂ => (z - p) ^ k * f z) (𝓝[≠] p) (𝓝 0)) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt f p := by
  have hpow : MeromorphicAt (fun z : ℂ => (z - p) ^ k) p := by fun_prop
  have hprod : MeromorphicAt (fun z : ℂ => (z - p) ^ k * f z) p := hpow.mul hf
  have hpos : 0 < meromorphicOrderAt (fun z : ℂ => (z - p) ^ k * f z) p :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hprod).mp hlim
  change meromorphicOrderAt ((fun z : ℂ => (z - p) ^ k) * f) p > 0 at hpos
  rw [meromorphicOrderAt_mul hpow hf] at hpos
  have hpowOrder : meromorphicOrderAt (fun z : ℂ => (z - p) ^ k) p =
      ((k : ℤ) : WithTop ℤ) := by
    simpa only using!
      (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
  rw [hpowOrder] at hpos
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [htop]
    exact WithTop.coe_lt_top (-(k : ℤ))
  · lift meromorphicOrderAt f p to ℤ using htop with q hq
    have hposInt : (0 : ℤ) < (k : ℤ) + q := by exact_mod_cast hpos
    exact_mod_cast (show -(k : ℤ) < q by omega)

/-- The divided difference of a function analytic at zero is itself analytic at zero. -/
theorem analyticAt_dslope_zero_of_analyticAt
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) :
    AnalyticAt ℂ (dslope U 0) 0 := by
  have hopen : IsOpen {z | AnalyticAt ℂ U z} := isOpen_analyticAt ℂ U
  have hdiff : DifferentiableOn ℂ U {z | AnalyticAt ℂ U z} :=
    fun z hz => hz.differentiableAt.differentiableWithinAt
  have hds : DifferentiableOn ℂ (dslope U 0) {z | AnalyticAt ℂ U z} :=
    (differentiableOn_dslope (hopen.mem_nhds hU)).mpr hdiff
  exact hds.analyticAt (hopen.mem_nhds hU)

/-- The `j`th derivative at zero of the analytic divided difference is the next derivative of the
original function divided by `j+1`. -/
theorem iteratedDeriv_dslope_zero_eq
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    iteratedDeriv j (dslope U 0) 0 =
      iteratedDeriv (j + 1) U 0 / ((j + 1 : ℕ) : ℂ) := by
  let V := dslope U 0
  have hV : AnalyticAt ℂ V 0 := analyticAt_dslope_zero_of_analyticAt hU
  have hfun : (fun x : ℂ => x * V x) = fun x => U x - U 0 := by
    funext x
    have hs := sub_smul_dslope U 0 x
    simpa only [V, sub_zero, smul_eq_mul] using hs
  have hder := congrArg (fun f : ℂ → ℂ => iteratedDeriv (j + 1) f 0) hfun
  have hleft : iteratedDeriv (j + 1) (fun x : ℂ => x * V x) 0 =
      ((j + 1 : ℕ) : ℂ) * iteratedDeriv j V 0 := by
    change iteratedDeriv (j + 1) ((id : ℂ → ℂ) * V) 0 = _
    rw [iteratedDeriv_mul contDiffAt_id (hV.contDiffAt.of_le le_top)]
    rw [Finset.sum_eq_single 1]
    · simp [iteratedDeriv_one]
    · intro k hk hk1
      have hk' : k ≤ j + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases hk0 : k = 0
      · subst k
        simp [iteratedDeriv_zero]
      · have hk2 : 2 ≤ k := by omega
        have hid : iteratedDeriv k (id : ℂ → ℂ) 0 = 0 := by
          rw [show k = (k - 2) + 1 + 1 by omega,
            iteratedDeriv_succ', iteratedDeriv_succ']
          simp
        rw [hid, mul_zero, zero_mul]
    · simp
  have hright : iteratedDeriv (j + 1) (fun x : ℂ => U x - U 0) 0 =
      iteratedDeriv (j + 1) U 0 := by
    have hconst : ContDiffAt ℂ (j + 1) (fun _ : ℂ => U 0) 0 := contDiffAt_const
    change iteratedDeriv (j + 1) (U - fun _ : ℂ => U 0) 0 = _
    rw [iteratedDeriv_sub (hU.contDiffAt.of_le le_top) hconst]
    simp only [iteratedDeriv_const, if_neg (Nat.add_one_ne_zero j), sub_zero]
  change iteratedDeriv (j + 1) (fun x : ℂ => x * V x) 0 =
    iteratedDeriv (j + 1) (fun x : ℂ => U x - U 0) 0 at hder
  rw [hleft, hright] at hder
  have hj : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  apply (eq_div_iff hj).2
  simpa [mul_comm] using hder

/-- **Complete divided-difference jet reflection.** Every derivative of the analytic remainder of
`U/x` is the corresponding shifted numerator derivative with its exact integral normalization. -/
theorem iteratedDeriv_iteratedDeriv_dslope_zero_eq
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j m : ℕ) :
    iteratedDeriv m (iteratedDeriv j (dslope U 0)) 0 =
      iteratedDeriv (j + m + 1) U 0 / ((j + m + 1 : ℕ) : ℂ) := by
  rw [congrFun (iteratedDeriv_comp_iterate (dslope U 0) m j) 0]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    iteratedDeriv_dslope_zero_eq hU (m + j)

/-- On the punctured germ, an analytic numerator over the coordinate is its residue pole plus its
analytic divided difference. -/
theorem div_id_eventuallyEq_const_mul_inv_add_dslope
    {U : ℂ → ℂ} :
    (fun x : ℂ => U x / x) =ᶠ[𝓝[≠] 0]
      (fun x => U 0 * x⁻¹ + dslope U 0 x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hs := sub_smul_dslope U 0 x
  simp only [sub_zero, smul_eq_mul] at hs
  have hds : dslope U 0 x = (U x - U 0) / x := by
    apply (eq_div_iff hx0).2
    simpa [mul_comm] using hs
  rw [hds]
  field_simp [hx0]
  ring

/-- **Complete differential principal-part law.** The `j`th derivative of `U/x` has exactly one
pole monomial; after subtracting it, the remainder is the `j`th derivative of the analytic divided
difference of `U`. -/
theorem iteratedDeriv_div_id_sub_principal_eventuallyEq
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    (fun x : ℂ => iteratedDeriv j (fun z => U z / z) x -
      U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1)) =ᶠ[𝓝[≠] 0]
      iteratedDeriv j (dslope U 0) := by
  have hdiv := div_id_eventuallyEq_const_mul_inv_add_dslope (U := U)
  have hderiv : iteratedDeriv j (fun x => U x / x) =ᶠ[𝓝[≠] 0]
      iteratedDeriv j (fun x => U 0 * x⁻¹ + dslope U 0 x) := by
    induction j with
    | zero => simpa [iteratedDeriv_zero] using hdiv
    | succ n ih =>
        rw [iteratedDeriv_succ, iteratedDeriv_succ]
        exact ih.nhdsNE_deriv
  have hds := analyticAt_dslope_zero_of_analyticAt hU
  have hdsevent : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      ContDiffAt ℂ j (dslope U 0) x :=
    nhdsWithin_le_nhds (hds.eventually_analyticAt.mono fun _ hx => hx.contDiffAt)
  filter_upwards [hderiv, hdsevent, self_mem_nhdsWithin] with x hder hdsx hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hinv : ContDiffAt ℂ j (fun z : ℂ => z⁻¹) x :=
    (contDiffAt_id (𝕜 := ℂ)).inv hx0
  have hconstInv :
      iteratedDeriv j (fun z : ℂ => U 0 * z⁻¹) x =
        U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1) := by
    rw [iteratedDeriv_const_mul_field (U 0) (fun z : ℂ => z⁻¹)]
    have hinvder := iteratedDeriv_inv_add_const 0 j x (by simpa using hx0)
    simp only [add_zero] at hinvder
    rw [hinvder, inv_pow]
    ring
  have hadd :
      iteratedDeriv j (fun z : ℂ => U 0 * z⁻¹ + dslope U 0 z) x =
        iteratedDeriv j (fun z : ℂ => U 0 * z⁻¹) x +
          iteratedDeriv j (dslope U 0) x := by
    simpa only [Pi.add_apply] using!
      iteratedDeriv_add (contDiffAt_const.mul hinv) hdsx
  rw [hder, hadd, hconstInv]
  ring

/-- The complete differential principal-part remainder has an explicit analytic extension. -/
theorem exists_analyticAt_iteratedDeriv_div_id_sub_principal
    {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (j : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      R 0 = iteratedDeriv (j + 1) U 0 / ((j + 1 : ℕ) : ℂ) ∧
      (fun x : ℂ => iteratedDeriv j (fun z => U z / z) x -
        U 0 * ((-1 : ℂ) ^ j * (j.factorial : ℂ)) * x⁻¹ ^ (j + 1)) =ᶠ[𝓝[≠] 0] R := by
  refine ⟨iteratedDeriv j (dslope U 0), ?_, iteratedDeriv_dslope_zero_eq hU j,
    iteratedDeriv_div_id_sub_principal_eventuallyEq hU j⟩
  have hds := analyticAt_dslope_zero_of_analyticAt hU
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hds
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- The `j`th derivative of a simple pole has exact order `-(j+1)`. -/
theorem meromorphicOrderAt_iteratedDeriv_of_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) (j : ℕ) :
    meromorphicOrderAt (iteratedDeriv j f) p =
      ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨c, hc, hlim⟩ := exists_tendsto_iteratedDeriv_of_meromorphic_simplePole hf horder j
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul (j + 1)
    (by rw [iteratedDeriv_eq_iterate]; exact hf.iterated_deriv) hc
  exact hlim

/-- Pointwise application of a constant-coefficient differential operator. -/
def constantCoeffDifferentialOperator (L : Polynomial ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => L.sum fun j a => a * iteratedDeriv j f z

theorem meromorphicAt_constantCoeffDifferentialOperator
    {L : Polynomial ℂ} {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    MeromorphicAt (constantCoeffDifferentialOperator L f) p := by
  unfold constantCoeffDifferentialOperator
  simp only [Polynomial.sum_def]
  have heq : (fun z : ℂ => ∑ n ∈ L.support, L.coeff n * iteratedDeriv n f z) =
      ∑ n ∈ L.support, fun z : ℂ => L.coeff n * iteratedDeriv n f z := by
    funext z
    exact (Finset.sum_apply z L.support
      (fun n z => L.coeff n * iteratedDeriv n f z)).symm
  rw [heq]
  apply MeromorphicAt.sum
  intro n hn
  have hd : MeromorphicAt (iteratedDeriv n f) p := by
    rw [iteratedDeriv_eq_iterate]
    exact hf.iterated_deriv
  exact (MeromorphicAt.const (L.coeff n) p).mul hd

theorem analyticAt_constantCoeffDifferentialOperator
    {L : Polynomial ℂ} {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (constantCoeffDifferentialOperator L f) p := by
  unfold constantCoeffDifferentialOperator
  simp only [Polynomial.sum_def]
  have heq : (fun z : ℂ => ∑ n ∈ L.support, L.coeff n * iteratedDeriv n f z) =
      ∑ n ∈ L.support, fun z : ℂ => L.coeff n * iteratedDeriv n f z := by
    funext z
    exact (Finset.sum_apply z L.support
      (fun n z => L.coeff n * iteratedDeriv n f z)).symm
  rw [heq]
  apply Finset.analyticAt_sum
  intro n hn
  have hd : AnalyticAt ℂ (iteratedDeriv n f) p := by
    rw [iteratedDeriv_eq_iterate]
    exact hf.iterated_deriv n
  exact analyticAt_const.mul hd

/-- A differential theta defect is analytic away from its two possible theta-zero lattices. This
form does not require a nonlattice hypothesis on the shift and is convenient for finite-family
separation arguments. -/
theorem analyticAt_constantCoeffDifferentialOperator_thetaLogDerivDefect_of_off_lattices
    {L : Polynomial ℂ} {τ h z : ℂ} (hτ : 0 < τ.im)
    (hbase : ∀ m n : ℤ, z ≠ thetaHalfPeriod τ + m + n * τ)
    (hshift : ∀ m n : ℤ, z ≠ thetaHalfPeriod τ + m + n * τ - h) :
    AnalyticAt ℂ
      (constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ)) z := by
  have hz0 : jacobiTheta₂ z τ ≠ 0 := by
    intro hzero
    obtain ⟨m, n, hmn⟩ :=
      (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
    exact hbase m n hmn
  have hzh0 : jacobiTheta₂ (z + h) τ ≠ 0 := by
    intro hzero
    obtain ⟨m, n, hmn⟩ :=
      (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
    apply hshift m n
    linear_combination hmn
  have hbaseAn := analyticAt_thetaLogDeriv_of_ne_zero hτ hz0
  have hshiftBase := analyticAt_thetaLogDeriv_of_ne_zero hτ hzh0
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
  have hshiftAn : AnalyticAt ℂ (fun w : ℂ => thetaLogDeriv (w + h) τ) z := by
    change AnalyticAt ℂ ((fun w => thetaLogDeriv w τ) ∘ fun w : ℂ => w + h) z
    exact AnalyticAt.comp (x := z) (g := fun w => thetaLogDeriv w τ)
      (f := fun w : ℂ => w + h) hshiftBase hinner
  have hdefAn : AnalyticAt ℂ (thetaLogDerivDefect h · τ) z := by
    simpa [thetaLogDerivDefect] using! hshiftAn.sub hbaseAn
  exact analyticAt_constantCoeffDifferentialOperator (L := L) hdefAn

/-- A common lower bound for the orders of finitely many meromorphic summands is a lower bound for
the order of their sum. -/
theorem le_meromorphicOrderAt_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (p : ℂ) (b : WithTop ℤ)
    (hmero : ∀ i ∈ s, MeromorphicAt (F i) p)
    (hbound : ∀ i ∈ s, b ≤ meromorphicOrderAt (F i) p) :
    b ≤ meromorphicOrderAt (∑ i ∈ s, F i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hFi := hmero i (Finset.mem_insert_self i s)
      have hsum : MeromorphicAt (∑ j ∈ s, F j) p :=
        MeromorphicAt.sum (fun j hj => hmero j (Finset.mem_insert_of_mem hj))
      have hadd := meromorphicOrderAt_add hFi hsum
      exact (le_min (hbound i (Finset.mem_insert_self i s))
        (ih (fun j hj => hmero j (Finset.mem_insert_of_mem hj))
          (fun j hj => hbound j (Finset.mem_insert_of_mem hj)))).trans hadd

/-- A nonzero constant-coefficient differential operator sends a simple pole to a pole of exact
order `degree(L)+1`; its top derivative cannot cancel against the less singular terms. -/
theorem meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole
    {L : Polynomial ℂ} (hL : L ≠ 0) {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt (constantCoeffDifferentialOperator L f) p =
      ((-((L.natDegree + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  let N := L.natDegree
  let term : ℕ → ℂ → ℂ := fun j z => L.coeff j * iteratedDeriv j f z
  have hNmem : N ∈ L.support := Polynomial.natDegree_mem_support_of_nonzero hL
  have htermMero : ∀ j : ℕ, MeromorphicAt (term j) p := by
    intro j
    have hd : MeromorphicAt (iteratedDeriv j f) p := by
      rw [iteratedDeriv_eq_iterate]
      exact hf.iterated_deriv
    exact (MeromorphicAt.const (L.coeff j) p).mul hd
  have htermOrder : ∀ j ∈ L.support,
      meromorphicOrderAt (term j) p =
        ((-((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    intro j hj
    have hc : L.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hmul := meromorphicOrderAt_mul_of_ne_zero
      (f := iteratedDeriv j f) (g := fun _ : ℂ => L.coeff j)
      (x := p) analyticAt_const hc
    change meromorphicOrderAt ((fun _ : ℂ => L.coeff j) * iteratedDeriv j f) p = _
    rw [hmul]
    exact meromorphicOrderAt_iteratedDeriv_of_simplePole hf horder j
  let R : Finset ℕ := L.support.erase N
  have hRmero : MeromorphicAt (∑ j ∈ R, term j) p :=
    MeromorphicAt.sum (fun j hj => htermMero j)
  have hRbound : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (∑ j ∈ R, term j) p := by
    apply le_meromorphicOrderAt_finset_sum R term p ((-(N : ℤ) : ℤ) : WithTop ℤ)
    · intro j hj
      exact htermMero j
    · intro j hj
      have hjS : j ∈ L.support := (Finset.mem_erase.mp hj).2
      have hjne : j ≠ N := (Finset.mem_erase.mp hj).1
      rw [htermOrder j hjS]
      have hjle : j ≤ N := Polynomial.le_natDegree_of_mem_supp j hjS
      exact_mod_cast (show -(N : ℤ) ≤ -((j + 1 : ℕ) : ℤ) by omega)
  have htopOrder : meromorphicOrderAt (term N) p =
      ((-((N + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := htermOrder N hNmem
  have hlt : meromorphicOrderAt (term N) p <
      meromorphicOrderAt (∑ j ∈ R, term j) p := by
    apply lt_of_lt_of_le _ hRbound
    rw [htopOrder]
    exact_mod_cast (show -((N + 1 : ℕ) : ℤ) < -(N : ℤ) by omega)
  have hsplit : constantCoeffDifferentialOperator L f =
      term N + ∑ j ∈ R, term j := by
    funext z
    rw [constantCoeffDifferentialOperator, Polynomial.sum_def]
    simp only [Pi.add_apply, Finset.sum_apply]
    change (∑ j ∈ L.support, term j z) = term N z + ∑ j ∈ R, term j z
    rw [← Finset.sum_erase_add _ _ hNmem, add_comm]
  rw [hsplit, meromorphicOrderAt_add_eq_left_of_lt hRmero hlt, htopOrder]

/-- **Exact differentiated theta-defect pole support.** Every nonzero constant-coefficient
differential operator preserves precisely the two theta-defect pole lattices and creates no new
poles. -/
theorem constantCoeffDifferentialOperator_thetaLogDerivDefect_pole_iff
    {L : Polynomial ℂ} (hL : L ≠ 0) {τ h z : ℂ}
    (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) :
    meromorphicOrderAt
        (constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ)) z < 0 ↔
      (∃ m n : ℤ, z = thetaHalfPeriod τ + m + n * τ) ∨
        ∃ m n : ℤ, z = thetaHalfPeriod τ + m + n * τ - h := by
  constructor
  · intro hpole
    by_contra hzclasses
    push Not at hzclasses
    have hz0 : jacobiTheta₂ z τ ≠ 0 := by
      intro hzero
      obtain ⟨m, n, hmn⟩ :=
        (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
      exact hzclasses.1 m n hmn
    have hzh0 : jacobiTheta₂ (z + h) τ ≠ 0 := by
      intro hzero
      obtain ⟨m, n, hmn⟩ :=
        (jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp hzero
      apply hzclasses.2 m n
      linear_combination hmn
    have hbaseAn := analyticAt_thetaLogDeriv_of_ne_zero hτ hz0
    have hshiftBase := analyticAt_thetaLogDeriv_of_ne_zero hτ hzh0
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
    have hshiftAn : AnalyticAt ℂ (fun w : ℂ => thetaLogDeriv (w + h) τ) z := by
      change AnalyticAt ℂ ((fun w => thetaLogDeriv w τ) ∘ fun w : ℂ => w + h) z
      exact AnalyticAt.comp (x := z) (g := fun w => thetaLogDeriv w τ)
        (f := fun w : ℂ => w + h) hshiftBase hinner
    have hdefAn : AnalyticAt ℂ (thetaLogDerivDefect h · τ) z := by
      simpa [thetaLogDerivDefect] using! hshiftAn.sub hbaseAn
    have hopAn := analyticAt_constantCoeffDifferentialOperator (L := L) hdefAn
    exact (not_lt_of_ge hopAn.meromorphicOrderAt_nonneg) hpole
  · rintro (⟨m, n, rfl⟩ | ⟨m, n, rfl⟩)
    · rw [meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hL
        (meromorphicAt_thetaLogDerivDefect hτ)
        (meromorphicOrderAt_thetaLogDerivDefect_base hτ hh m n)]
      exact_mod_cast (show -((L.natDegree + 1 : ℕ) : ℤ) < 0 by
        have : 0 < L.natDegree + 1 := by omega
        omega)
    · rw [meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hL
        (meromorphicAt_thetaLogDerivDefect hτ)
        (meromorphicOrderAt_thetaLogDerivDefect_shifted hτ hh m n)]
      exact_mod_cast (show -((L.natDegree + 1 : ℕ) : ℤ) < 0 by
        have : 0 < L.natDegree + 1 := by omega
        omega)

end

end GaloisForLFunctions
