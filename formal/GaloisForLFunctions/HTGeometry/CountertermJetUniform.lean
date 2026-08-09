import GaloisForLFunctions.HTGeometry.CountertermJetSeries

/-!
# Uniformity of the counterterm jet

The jet series is dominated by a geometric series whose ratio is the nome product times the
coordinate, and its leading term differs from the limit only through a numerical infinite product.
Both estimates are monotone in the modulus of the coordinate, so the jet limit is uniform on every
ball of coordinates.

Reading the coordinate as the reciprocal of the point turns this into uniform convergence of the
counterterm jet on every region bounded away from the origin, at every counterterm order.  Local
uniformity on the punctured plane follows, since every compact subset avoiding the origin lies in
such a region.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The counterterm-jet quotient: the free-energy tail of a finite section with the first `j`
counterterms subtracted, divided by the `N`th power of the nome product. -/
noncomputable def countertermJetQuotient {ι : Type*} (g : ℕ) (p : ι → ℂ) (j N : ℕ)
    (S : Finset ι) (x : ℂ) : ℂ :=
  (-sectionLogTail g p S ((∏ a ∈ S, p a) / x)
      + ∑ m ∈ Finset.range j, ((∏ a ∈ S, p a) / x) ^ (m + (g + 1)) /
          ((m + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹) /
    (∏ a ∈ S, p a) ^ N

/-- The `N`th counterterm-jet coefficient. -/
noncomputable def countertermJetCoeff {ι : Type*} (p : ι → ℂ) (N : ℕ) (x : ℂ) : ℂ :=
  -((x⁻¹) ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹)

/-- **The jet limit is uniform on balls.**  On every ball of coordinates the jet series converges
uniformly to the leading coefficient of the counterterm jet. -/
theorem tendstoUniformlyOn_jetSeries {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : g + 1 ≤ N) :
    TendstoUniformlyOn (fun (S : Finset ι) (y : ℂ) => jetSeries p S y N)
      (fun y : ℂ => y ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹)
      atTop (Metric.closedBall (0 : ℂ) M) := by
  classical
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hB0 : (0 : ℝ) ≤ ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ :=
    le_trans (norm_nonneg _)
      (norm_finiteEulerProduct_le g p hp_lt hsum ∅ (k := g + 1) le_rfl)
  have huN_lt : ∀ a, ‖p a ^ N‖ < 1 := by
    intro a
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hp_lt a) (by omega)
  have huN_sum : Summable (fun a => ‖p a ^ N‖) := by
    simpa only [norm_pow] using summable_norm_pow_of_le hp_lt hN hsum
  have hprodN : HasProd (fun a => (1 - p a ^ N)⁻¹) (∏' a, (1 - p a ^ N)⁻¹) :=
    (hasProd_inv_one_sub_nome (fun a => p a ^ N) huN_lt huN_sum).multipliable.hasProd
  have hQn : Tendsto (fun S : Finset ι => ‖∏ a ∈ S, p a‖) atTop (𝓝 0) := by
    simpa using (tendsto_nomeProduct_atTop_zero g p hp_lt hsum).norm
  have hPn : Tendsto (fun S : Finset ι =>
      ‖(∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹‖) atTop (𝓝 0) := by
    have h : Tendsto (fun S : Finset ι =>
        (∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹) atTop (𝓝 0) := by
      simpa using hprodN.sub_const (∏' a, (1 - p a ^ N)⁻¹)
    simpa using h.norm
  have hb : Tendsto (fun S : Finset ι =>
      ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N) * (2 * (‖∏ a ∈ S, p a‖ * M))
        + M ^ N / (N : ℝ) *
            ‖(∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : Finset ι =>
        ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N) *
          (2 * (‖∏ a ∈ S, p a‖ * M))) atTop (𝓝 0) := by
      have h := ((hQn.mul_const M).const_mul (2 : ℝ)).const_mul
        ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N)
      simpa using h
    have h2 : Tendsto (fun S : Finset ι => M ^ N / (N : ℝ) *
        ‖(∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹‖) atTop (𝓝 0) := by
      simpa using hPn.const_mul (M ^ N / (N : ℝ))
    simpa using h1.add h2
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hQM : Tendsto (fun S : Finset ι => ‖∏ a ∈ S, p a‖ * M) atTop (𝓝 0) := by
    simpa using hQn.mul_const M
  have hhalf : ∀ᶠ S : Finset ι in atTop, ‖∏ a ∈ S, p a‖ * M ≤ 1 / 2 := by
    have h := hQM.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    exact h.mono fun S hS => le_of_lt hS
  filter_upwards [hb.eventually (gt_mem_nhds hε), hhalf] with S hbS hSh
  intro y hy
  have hyM : ‖y‖ ≤ M := by simpa using hy
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have hQ0 : (0 : ℝ) ≤ ‖∏ a ∈ S, p a‖ := norm_nonneg _
  have hrle : ‖∏ a ∈ S, p a‖ * ‖y‖ ≤ ‖∏ a ∈ S, p a‖ * M :=
    mul_le_mul_of_nonneg_left hyM hQ0
  have hrhalf : ‖∏ a ∈ S, p a‖ * ‖y‖ ≤ 1 / 2 := hrle.trans hSh
  have hr0 : (0 : ℝ) ≤ ‖∏ a ∈ S, p a‖ * ‖y‖ := by positivity
  have hcontr : ‖∏ a ∈ S, p a‖ * ‖y‖ < 1 := by linarith
  have hhead := norm_jetSeries_sub_head_le g p hp_lt hsum S (y := y) hN hcontr
  have hyN : ‖y‖ ^ N ≤ M ^ N := pow_le_pow_left₀ hy0 hyM N
  -- the geometric tail factor
  have hgeo : (‖∏ a ∈ S, p a‖ * ‖y‖) / (1 - ‖∏ a ∈ S, p a‖ * ‖y‖)
      ≤ 2 * (‖∏ a ∈ S, p a‖ * M) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hcoef : ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N)
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N) := by
    have : (0 : ℝ) ≤ (∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hyN this
  have hsecond : ‖jetSeries p S y N - y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹‖
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N) *
          (2 * (‖∏ a ∈ S, p a‖ * M)) := by
    refine hhead.trans (mul_le_mul hcoef hgeo ?_ ?_)
    · positivity
    · positivity
  have hfirstval : ‖y ^ N / (N : ℂ)‖ = ‖y‖ ^ N / (N : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
  have hfirst : ‖y ^ N / (N : ℂ) *
      ((∏' a, (1 - p a ^ N)⁻¹) - ∏ a ∈ S, (1 - p a ^ N)⁻¹)‖
      ≤ M ^ N / (N : ℝ) * ‖(∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹‖ := by
    rw [norm_mul, hfirstval, ← norm_neg ((∏' a, (1 - p a ^ N)⁻¹) - ∏ a ∈ S, (1 - p a ^ N)⁻¹),
      neg_sub]
    exact mul_le_mul_of_nonneg_right (by gcongr) (norm_nonneg _)
  have hdist : dist (y ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹) (jetSeries p S y N)
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * M ^ N) * (2 * (‖∏ a ∈ S, p a‖ * M))
        + M ^ N / (N : ℝ) *
            ‖(∏ a ∈ S, (1 - p a ^ N)⁻¹) - ∏' a, (1 - p a ^ N)⁻¹‖ := by
    rw [dist_eq_norm]
    have hid : y ^ N / (N : ℂ) * ∏' a, (1 - p a ^ N)⁻¹ - jetSeries p S y N
        = (y ^ N / (N : ℂ) *
            ((∏' a, (1 - p a ^ N)⁻¹) - ∏ a ∈ S, (1 - p a ^ N)⁻¹))
          + -(jetSeries p S y N - y ^ N / (N : ℂ) * ∏ a ∈ S, (1 - p a ^ N)⁻¹) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith
  exact lt_of_le_of_lt hdist hbS

/-- **The counterterm jet is uniform away from the origin.**  For every counterterm order and every
positive lower bound on the modulus of the point, the counterterm jet converges uniformly on that
region; in particular it converges locally uniformly on the punctured plane. -/
theorem tendstoUniformlyOn_countertermJet {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) {c : ℝ} (hc : 0 < c)
    {N j : ℕ} (hj : j + (g + 1) = N) :
    TendstoUniformlyOn (countertermJetQuotient g p j N) (countertermJetCoeff p N)
      atTop {x : ℂ | c ≤ ‖x‖} := by
  classical
  have hQne : ∀ S : Finset ι, (∏ a ∈ S, p a) ≠ 0 :=
    fun S => Finset.prod_ne_zero_iff.mpr fun a _ => hp_ne a
  have hsub : {x : ℂ | c ≤ ‖x‖} ⊆ (fun x : ℂ => x⁻¹) ⁻¹' Metric.closedBall (0 : ℂ) c⁻¹ := by
    intro x hx
    have hx' : c ≤ ‖x‖ := hx
    have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le hc hx'
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_inv]
    exact (inv_le_inv₀ hxpos hc).mpr hx'
  have hbase := (tendstoUniformlyOn_jetSeries g p hp_lt hsum
    (M := c⁻¹) (by positivity) (N := N) (by omega)).comp (fun x : ℂ => x⁻¹)
  have hmono := hbase.mono hsub
  have hneg := hmono.neg
  refine hneg.congr ?_
  have hQn : Tendsto (fun S : Finset ι => ‖∏ a ∈ S, p a‖) atTop (𝓝 0) := by
    simpa using (tendsto_nomeProduct_atTop_zero g p hp_lt hsum).norm
  have hev : ∀ᶠ S : Finset ι in atTop, ‖∏ a ∈ S, p a‖ < c :=
    hQn.eventually (eventually_lt_nhds hc)
  filter_upwards [hev] with S hS
  intro x hx
  have hx' : c ≤ ‖x‖ := hx
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx'
    linarith
  have hlt : ‖(∏ a ∈ S, p a) / x‖ < 1 := by
    rw [norm_div, div_lt_one (by positivity)]
    linarith
  have hsplit := sectionLogTail_split g p hp_lt hsum S hlt j
  have htail := sectionLogTail_tail_eq g p S x hj
  have hnum : -sectionLogTail g p S ((∏ a ∈ S, p a) / x)
      + ∑ m ∈ Finset.range j, ((∏ a ∈ S, p a) / x) ^ (m + (g + 1)) /
          ((m + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹
      = -((∏ a ∈ S, p a) ^ N * jetSeries p S x⁻¹ N) := by
    rw [hsplit, ← htail]
    ring
  show -jetSeries p S x⁻¹ N
      = (-sectionLogTail g p S ((∏ a ∈ S, p a) / x)
          + ∑ m ∈ Finset.range j, ((∏ a ∈ S, p a) / x) ^ (m + (g + 1)) /
              ((m + (g + 1) : ℕ) : ℂ) * ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹) /
          (∏ a ∈ S, p a) ^ N
  rw [hnum, neg_div, mul_div_cancel_left₀ _ (pow_ne_zero N (hQne S))]

/-- **Uniform convergence of the counterterm jet on every compact set avoiding the origin.** -/
theorem tendstoUniformlyOn_countertermJet_of_isCompact {ι : Type*} [Infinite ι] (g : ℕ)
    (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) {K : Set ℂ} (hK : IsCompact K)
    (h0 : (0 : ℂ) ∉ K) {N j : ℕ} (hj : j + (g + 1) = N) :
    TendstoUniformlyOn (countertermJetQuotient g p j N) (countertermJetCoeff p N) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hK.exists_isMinOn hne (f := fun z : ℂ => ‖z‖) continuous_norm.continuousOn
  have hx₀ne : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀K)
  have hc : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀ne
  refine (tendstoUniformlyOn_countertermJet g p hp_ne hp_lt hsum hc hj).mono ?_
  intro z hz
  exact hx₀min hz

/-- **The counterterm jet converges locally uniformly on the punctured plane**, at every
counterterm order. -/
theorem tendstoLocallyUniformlyOn_countertermJet {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) {N j : ℕ} (hj : j + (g + 1) = N) :
    TendstoLocallyUniformlyOn (countertermJetQuotient g p j N) (countertermJetCoeff p N)
      atTop {x : ℂ | x ≠ 0} := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne).mpr ?_
  intro K hKs hK
  exact tendstoUniformlyOn_countertermJet_of_isCompact g p hp_ne hp_lt hsum hK
    (fun h => (hKs h) rfl) hj

end HTGeometry
