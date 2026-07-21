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
    simpa only using (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
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
      simpa only using
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
    simpa only using
      (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := p) (n := k))
  rw [hpowOrder] at hpos
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [htop]
    exact WithTop.coe_lt_top (-(k : ℤ))
  · lift meromorphicOrderAt f p to ℤ using htop with q hq
    have hposInt : (0 : ℤ) < (k : ℤ) + q := by exact_mod_cast hpos
    exact_mod_cast (show -(k : ℤ) < q by omega)

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
    simpa [thetaLogDerivDefect] using hshiftAn.sub hbaseAn
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
      simpa [thetaLogDerivDefect] using hshiftAn.sub hbaseAn
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
