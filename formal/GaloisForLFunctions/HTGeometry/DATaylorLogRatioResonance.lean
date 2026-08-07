import GaloisForLFunctions.HTGeometry.StretchedExponentialIntegerDominance
import GaloisForLFunctions.HTGeometry.LogRatioResonance
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence

/-!
# Differential-algebraic Taylor log-ratio resonance

This file proves the finite log-ratio law for Taylor coefficients.  Starting from an
integer-normalized algebraic differential relation, balanced coefficient atoms yield two
near-minimal valuations in a fixed translated window.  Finite pigeonhole then freezes their
multiplicity difference into a nonzero integer polynomial `Q`; the logarithmic valuation defect
is negligible against the geometric log-magnitude scale, so `Q(1) = Q(lam) = 0`.

Consequently every finite successive log-magnitude ratio `lam > 1` of a differentially algebraic
series is algebraic.  A transcendental such limit forces hypertranscendence, while the existing
log-superlacunary theorem excludes an infinite ratio from the DA spectrum.
-/

open Filter Finset PowerSeries MvPolynomial Polynomial Topology

namespace GaloisForLFunctions

noncomputable section

/-- A fixed geometric sequence of ratio greater than one beats the linear scale. -/
theorem tendsto_const_pow_div_natCast_atTop {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / n) atTop atTop := by
  have hsmall : Tendsto (fun n : ℕ => (n : ℝ) / r ^ n) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have hmem : ∀ᶠ n : ℕ in atTop, (n : ℝ) / r ^ n ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_pos (by exact_mod_cast hn) (pow_pos (lt_trans zero_lt_one hr) n)
  have hwithin : Tendsto (fun n : ℕ => (n : ℝ) / r ^ n) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hmem⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Function.comp_apply]
  rw [inv_div]

/-- Iterating an eventual lower bound on successive ratios. -/
theorem ratio_iterate_lower_bound {b : ℕ → ℝ} {r : ℝ} {N n k : ℕ}
    (hr0 : 0 ≤ r) (hpos : ∀ m ≥ N, 0 < b m)
    (hratio : ∀ m ≥ N, r ≤ b (m + 1) / b m) (hn : N ≤ n) :
    r ^ k * b n ≤ b (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hnk : N ≤ n + k := hn.trans (Nat.le_add_right n k)
      have hstep : r * b (n + k) ≤ b (n + k + 1) := by
        have hr := hratio (n + k) hnk
        rwa [le_div_iff₀ (hpos (n + k) hnk)] at hr
      calc
        r ^ (k + 1) * b n = r * (r ^ k * b n) := by ring
        _ ≤ r * b (n + k) := mul_le_mul_of_nonneg_left ih hr0
        _ ≤ b (n + k + 1) := hstep

/-- Iterating an eventual upper bound on successive ratios. -/
theorem ratio_iterate_upper_bound {b : ℕ → ℝ} {R : ℝ} {N n k : ℕ}
    (hR0 : 0 ≤ R) (hpos : ∀ m ≥ N, 0 < b m)
    (hratio : ∀ m ≥ N, b (m + 1) / b m ≤ R) (hn : N ≤ n) :
    b (n + k) ≤ R ^ k * b n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hnk : N ≤ n + k := hn.trans (Nat.le_add_right n k)
      have hstep : b (n + k + 1) ≤ R * b (n + k) := by
        have hr := hratio (n + k) hnk
        rwa [div_le_iff₀ (hpos (n + k) hnk)] at hr
      calc
        b (n + (k + 1)) = b (n + k + 1) := by simp only [Nat.add_assoc]
        _ ≤ R * b (n + k) := hstep
        _ ≤ R * (R ^ k * b n) := mul_le_mul_of_nonneg_left ih hR0
        _ = R ^ (k + 1) * b n := by ring

/-- A finite ratio limit greater than one supplies uniform geometric lower and upper steps on a
positive tail. -/
theorem exists_eventually_geometric_ratio_bounds {b : ℕ → ℝ} {lam : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (hlam1 : 1 < lam) :
    ∃ r R : ℝ, 1 < r ∧ lam < R ∧ ∃ N : ℕ, ∀ n ≥ N,
      0 < b n ∧ r * b n ≤ b (n + 1) ∧ b (n + 1) ≤ R * b n := by
  let r : ℝ := (1 + lam) / 2
  let R : ℝ := lam + 1
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrlam : r < lam := by dsimp [r]; linarith
  have hlamR : lam < R := by dsimp [R]; linarith
  have hlower : ∀ᶠ n in atTop, r ≤ b (n + 1) / b n :=
    (hlam.eventually (Ioi_mem_nhds hrlam)).mono fun _ h => h.le
  have hupper : ∀ᶠ n in atTop, b (n + 1) / b n ≤ R :=
    (hlam.eventually (Iio_mem_nhds hlamR)).mono fun _ h => h.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hpos.and (hlower.and hupper))
  refine ⟨r, R, hr1, hlamR, N, fun n hn => ?_⟩
  obtain ⟨hbn, hlo, hup⟩ := hN n hn
  constructor
  · exact hbn
  constructor
  · rwa [le_div_iff₀ hbn] at hlo
  · rwa [div_le_iff₀ hbn] at hup

/-- A positive sequence with a finite successive-ratio limit greater than one beats the linear
scale. -/
theorem tendsto_div_natCast_atTop_of_ratio_tendsto_gt_one {b : ℕ → ℝ} {lam : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (hlam1 : 1 < lam) :
    Tendsto (fun n => b n / n) atTop atTop := by
  let r : ℝ := (1 + lam) / 2
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrlam : r < lam := by dsimp [r]; linarith
  have hratio : ∀ᶠ n in atTop, r ≤ b (n + 1) / b n :=
    (hlam.eventually (Ioi_mem_nhds hrlam)).mono fun _ h => h.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hpos.and hratio)
  have hgeo : ∀ k : ℕ, r ^ k * b N ≤ b (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hNk := hN (N + k) (by omega)
      have hstep : r * b (N + k) ≤ b (N + k + 1) := by
        rw [le_div_iff₀ hNk.1] at hNk
        exact hNk.2
      calc
        r ^ (k + 1) * b N = r * (r ^ k * b N) := by ring
        _ ≤ r * b (N + k) := mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hr1))
        _ ≤ b (N + k + 1) := hstep
  have hbN : 0 < b N := (hN N le_rfl).1
  have hc : 0 < b N / r ^ N := div_pos hbN (pow_pos (lt_trans zero_lt_one hr1) N)
  have hmin : Tendsto (fun n : ℕ => (b N / r ^ N) * (r ^ n / n)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (tendsto_const_pow_div_natCast_atTop hr1)
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hnN hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgn := hgeo (n - N)
  rw [show N + (n - N) = n by omega] at hgn
  have hpow : r ^ (n - N) = r ^ n / r ^ N :=
    pow_sub₀ r (ne_of_gt (lt_trans zero_lt_one hr1)) hnN
  rw [hpow] at hgn
  have hquot : (r ^ n / r ^ N) * b N / n ≤ b n / n := by
    exact div_le_div_of_nonneg_right hgn hnpos.le
  calc
    (b N / r ^ N) * (r ^ n / n) = (r ^ n / r ^ N) * b N / n := by ring
    _ ≤ b n / n := hquot

/-- Under a finite successive-ratio limit greater than one, the sequence beats every fixed
polynomial scale. -/
theorem exists_const_mul_pow_lt_of_ratio_tendsto_gt_one {b : ℕ → ℝ} {lam : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (A : ℝ) (hA : 0 < A) (C E : ℕ) (hC : 0 < C) :
    ∃ Q₀ : ℕ, ∀ q ≥ Q₀,
      A * (((C * (q + 1)) ^ E : ℕ) : ℝ) < b q := by
  obtain ⟨r, R, hr1, _hlamR, N, hbounds⟩ :=
    exists_eventually_geometric_ratio_bounds hpos hlam hlam1
  have hr0 : 0 ≤ r := (zero_lt_one.trans hr1).le
  have htailpos : ∀ m ≥ N, 0 < b m := fun m hm => (hbounds m hm).1
  have htailratio : ∀ m ≥ N, r ≤ b (m + 1) / b m := by
    intro m hm
    have h := (hbounds m hm).2.1
    rwa [le_div_iff₀ (htailpos m hm)]
  let c : ℝ := b N / r ^ N
  have hc : 0 < c := div_pos (htailpos N le_rfl) (pow_pos (zero_lt_one.trans hr1) N)
  let K : ℝ := A * (C : ℝ) ^ E * 2 ^ E / c
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hlittle : (fun q : ℕ => K * (q : ℝ) ^ E) =o[atTop] fun q => r ^ q :=
    (isLittleO_pow_const_const_pow_of_one_lt E hr1).const_mul_left K
  have hright : ∀ᶠ q : ℕ in atTop, 0 < ‖r ^ q‖ :=
    Filter.Eventually.of_forall fun q => norm_pos_iff.mpr (pow_ne_zero q (ne_of_gt (zero_lt_one.trans hr1)))
  have hlt : ∀ᶠ q : ℕ in atTop, K * (q : ℝ) ^ E < r ^ q := by
    filter_upwards [hlittle.eventuallyLT_norm_of_eventually_pos hright,
      eventually_ge_atTop 1] with q hq hq1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (mul_pos hK (pow_pos (by exact_mod_cast hq1) E)),
      abs_of_pos (pow_pos (zero_lt_one.trans hr1) q)] at hq
    exact hq
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.mp hlt
  refine ⟨max N (max Q₁ 1), fun q hq => ?_⟩
  have hqN : N ≤ q := (le_max_left _ _).trans hq
  have hqQ₁ : Q₁ ≤ q := (le_trans (le_max_left _ _) (le_max_right N _)).trans hq
  have hq1 : 1 ≤ q := (le_trans (le_max_right _ _) (le_max_right N _)).trans hq
  have hqcast : (q + 1 : ℕ) ≤ 2 * q := by omega
  have hpoly :
      A * (((C * (q + 1)) ^ E : ℕ) : ℝ) ≤
        A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E := by
    push_cast
    have hcast : (q : ℝ) + 1 ≤ 2 * q := by exact_mod_cast hqcast
    calc
      A * ((C : ℝ) * ((q : ℝ) + 1)) ^ E
          ≤ A * ((C : ℝ) * (2 * (q : ℝ))) ^ E := by
            gcongr
      _ = A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E := by ring
  have hscaled : A * (C : ℝ) ^ E * 2 ^ E * (q : ℝ) ^ E < c * r ^ q := by
    have h := mul_lt_mul_of_pos_left (hQ₁ q hqQ₁) hc
    dsimp [K] at h
    field_simp [ne_of_gt hc] at h
    simpa only [mul_assoc] using h
  have hgeo := ratio_iterate_lower_bound (N := N) (n := N) (k := q - N)
    hr0 htailpos htailratio le_rfl
  have hpow : r ^ (q - N) = r ^ q / r ^ N :=
    pow_sub₀ r (ne_of_gt (zero_lt_one.trans hr1)) hqN
  rw [hpow] at hgeo
  have hcgeo : c * r ^ q ≤ b q := by
    dsimp [c]
    calc
      b N / r ^ N * r ^ q = (r ^ q / r ^ N) * b N := by ring
      _ ≤ b q := by simpa [Nat.add_sub_of_le hqN] using hgeo
  exact hpoly.trans_lt (hscaled.trans_le hcgeo)

/-- The index-mass constraint forces every lower-degree atom a fixed linear distance beyond the
balanced top-degree scale. -/
theorem lowerDegree_max_ge_ratio_factor {D q J Z imax : ℕ}
    (hcount : 2 ≤ D)
    (hDqMax : D * q ≤ imax * (D - 1) + J + Z)
    (hqthreshold : 2 * (J + Z) + 2 ≤ q) :
    (1 + 1 / (2 * (D : ℝ))) * (q : ℝ) ≤ (imax : ℝ) := by
  have hD : 0 < D := lt_of_lt_of_le two_pos hcount
  by_contra hnot
  have hlt : (imax : ℝ) < (1 + 1 / (2 * (D : ℝ))) * (q : ℝ) := lt_of_not_ge hnot
  have hDsub : (((D - 1 : ℕ) : ℝ)) = (D : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ D by omega)]
    norm_num
  have hmul : (imax : ℝ) * ((D - 1 : ℕ) : ℝ) <
      ((1 + 1 / (2 * (D : ℝ))) * (q : ℝ)) * ((D - 1 : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right hlt (by exact_mod_cast (show 0 < D - 1 by omega))
  have hfactor : (((D - 1 : ℕ) : ℝ)) * (1 + 1 / (2 * (D : ℝ))) ≤
      (D : ℝ) - 1 / 2 := by
    rw [hDsub]
    exact lowerDegree_factor_le hD
  have hfactorq : (((D - 1 : ℕ) : ℝ)) * (1 + 1 / (2 * (D : ℝ))) * (q : ℝ) ≤
      ((D : ℝ) - 1 / 2) * (q : ℝ) :=
    mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hJZtwo : (2 : ℝ) * ((J + Z : ℕ) : ℝ) < (q : ℝ) := by
    have hnat : 2 * (J + Z) < q := by omega
    exact_mod_cast hnat
  have hJZ : ((J + Z : ℕ) : ℝ) < (q : ℝ) / 2 := by linarith
  have hDqMaxR : (D : ℝ) * q ≤
      (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z := by
    exact_mod_cast hDqMax
  have hupper : (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z <
      (D : ℝ) * q := by
    calc
      (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z <
          (((1 + 1 / (2 * (D : ℝ))) * (q : ℝ)) * ((D - 1 : ℕ) : ℝ)) + J + Z := by
            linarith
      _ = (((D - 1 : ℕ) : ℝ) * (1 + 1 / (2 * (D : ℝ)))) * (q : ℝ) +
          (J + Z : ℕ) := by
            push_cast
            ring
      _ ≤ ((D : ℝ) - 1 / 2) * (q : ℝ) + (J + Z : ℕ) := by
            gcongr
      _ < (D : ℝ) * q := by linarith
  exact (not_lt_of_ge hDqMaxR) hupper

theorem balanced_level_tail_ineq {D q K J Z N : ℕ} (hD : 0 < D)
    (hq : (D - 1) * K + J + Z ≤ q) (hDqN : D * q ≤ N + J)
    (hNZ : Z ≤ N) :
    q - ((D - 1) * K + J + Z) + (D - 1) * (q + K) ≤ N - Z := by
  have hleft :
      q - ((D - 1) * K + J + Z) + (D - 1) * (q + K) + J + Z = D * q := by
    have hsub : q - ((D - 1) * K + J + Z) + ((D - 1) * K + J + Z) = q :=
      Nat.sub_add_cancel hq
    calc
      q - ((D - 1) * K + J + Z) + (D - 1) * (q + K) + J + Z =
          (q - ((D - 1) * K + J + Z) + ((D - 1) * K + J + Z)) +
            (D - 1) * q := by ring
      _ = q + (D - 1) * q := by rw [hsub]
      _ = ((D - 1) + 1) * q := by ring
      _ = D * q := by rw [Nat.sub_add_cancel (show 1 ≤ D by omega)]
  omega

/-- Any nonzero ADE atom lying within the logarithmic bend window of a balanced top-degree witness
has maximal jet degree and remains in a fixed upper offset window. -/
theorem near_balanced_atom_count_eq_and_supportMax_lt
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    {r R : ℝ} (hr1 : 1 < r) (hR1 : 1 < R)
    {Ntail : ℕ}
    (hratioLower : ∀ m ≥ Ntail, r ≤ b (m + 1) / b m)
    (hratioUpper : ∀ m ≥ Ntail, b (m + 1) / b m ≤ R)
    {n N D J q K : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (δ : Fin D → ℕ) {P : ℝ} {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hnear : ν.sum (fun i k => (k : ℝ) * b i) <
      (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) +
        Real.log (P + 1))
    (hlog : Real.log (P + 1) ≤ b q)
    (hDqN : D * q ≤ N + J) (hNZ : magnitudeMaxXDegree Q < N) (hqtail : Ntail ≤ q)
    (hqthreshold : max (2 * (J + magnitudeMaxXDegree Q) + 2) (2 * D * K) ≤ q)
    (hK : (D : ℝ) * R ^ magnitudeOffsetMax δ + 1 < r ^ K) :
    ν.sum (fun _ k => k) = D ∧
      ν.support.max' (appearing_atom_support_nonempty_of_maxX_lt_level Q hν
        hNZ) < q + K := by
  let hsupp : ν.support.Nonempty :=
    appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ
  let imax := ν.support.max' hsupp
  have hR0 : 0 ≤ R := (zero_lt_one.trans hR1).le
  have hr0 : 0 ≤ r := (zero_lt_one.trans hr1).le
  have hWval :
      (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) ≤
        (D : ℝ) * R ^ magnitudeOffsetMax δ * b q := by
    rw [valuation_eq_key_sum]
    calc
      ∑ i : Fin D, b (q + δ i) ≤
          ∑ _i : Fin D, R ^ magnitudeOffsetMax δ * b q := by
            apply Finset.sum_le_sum
            intro i _
            have hi := ratio_iterate_upper_bound (N := Ntail) (n := q) (k := δ i)
              hR0 (fun m _ => hbpos m) hratioUpper hqtail
            exact hi.trans (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ hR1.le (offset_le_magnitudeOffsetMax δ i))
              (hbpos q).le)
      _ = (D : ℝ) * R ^ magnitudeOffsetMax δ * b q := by
        simp [Finset.card_univ]
        ring
  have hfar : q + K ≤ imax → False := by
    intro hqK
    have hqimax : q ≤ imax := (Nat.le_add_right q K).trans hqK
    have hKdiff : K ≤ imax - q := by omega
    have hgeo := ratio_iterate_lower_bound (N := Ntail) (n := q) (k := imax - q)
      hr0 (fun m _ => hbpos m) hratioLower hqtail
    have hqadd : q + (imax - q) = imax := Nat.add_sub_of_le hqimax
    rw [hqadd] at hgeo
    have hpow : r ^ K ≤ r ^ (imax - q) := pow_le_pow_right₀ hr1.le hKdiff
    have hpowb : r ^ K * b q ≤ b imax :=
      (mul_le_mul_of_nonneg_right hpow (hbpos q).le).trans hgeo
    have hvalMax : b imax ≤ ν.sum (fun i k => (k : ℝ) * b i) := by
      simpa [imax] using valuation_ge_b_max (fun i => (hbpos i).le) hsupp
    have hscale :
        ((D : ℝ) * R ^ magnitudeOffsetMax δ + 1) * b q < r ^ K * b q :=
      mul_lt_mul_of_pos_right hK (hbpos q)
    have hnear' : ν.sum (fun i k => (k : ℝ) * b i) <
        ((D : ℝ) * R ^ magnitudeOffsetMax δ + 1) * b q := by
      calc
        ν.sum (fun i k => (k : ℝ) * b i) <
            (key (fun i : Fin D => q + δ i)).sum (fun i k => (k : ℝ) * b i) +
              Real.log (P + 1) := hnear
        _ ≤ (D : ℝ) * R ^ magnitudeOffsetMax δ * b q + b q :=
          add_le_add hWval hlog
        _ = ((D : ℝ) * R ^ magnitudeOffsetMax δ + 1) * b q := by ring
    exact (not_lt_of_ge (hpowb.trans hvalMax)) (hscale.trans' hnear')
  have hcountle := appearing_atom_count_le Q hν
  rw [← hDmax] at hcountle
  have hcount : ν.sum (fun _ k => k) = D := by
    rcases hcountle.eq_or_lt with heq | hlt
    · exact heq
    · by_cases hDone : D = 1
      · have hzero : ν.sum (fun _ k => k) = 0 := by omega
        obtain ⟨i, hi⟩ := hsupp
        have hibound := finsupp_apply_le_count ν i
        rw [hzero] at hibound
        exact False.elim ((Finsupp.mem_support_iff.mp hi) (Nat.eq_zero_of_le_zero hibound))
      · have hDtwo : 2 ≤ D := by omega
        have hcountSmall : ν.sum (fun _ k => k) ≤ D - 1 := by omega
        have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
        have hweightMax := weighted_sum_le_max_mul_count hsupp
        have hweightUpper : ν.sum (fun i k => i * k) ≤ imax * (D - 1) :=
          hweightMax.trans (Nat.mul_le_mul_left imax hcountSmall)
        have hDqMax : D * q ≤
            imax * (D - 1) + J + magnitudeMaxXDegree Q := by
          have hNsplit : N - magnitudeMaxXDegree Q + magnitudeMaxXDegree Q = N :=
            Nat.sub_add_cancel hNZ.le
          omega
        have hfactor := lowerDegree_max_ge_ratio_factor hDtwo hDqMax
          ((le_max_left _ _).trans hqthreshold)
        have hqDK : 2 * D * K ≤ q := (le_max_right _ _).trans hqthreshold
        have hDr : (0 : ℝ) < 2 * D := by positivity
        have hKq : (K : ℝ) ≤ (q : ℝ) / (2 * D : ℕ) := by
          rw [le_div_iff₀]
          · have hnat : K * (2 * D) ≤ q := by
              calc
                K * (2 * D) = 2 * D * K := by ring
                _ ≤ q := hqDK
            exact_mod_cast hnat
          · exact_mod_cast (show 0 < 2 * D by omega)
        have hqKreal : ((q + K : ℕ) : ℝ) ≤ (imax : ℝ) := by
          push_cast
          have hsplit :
              (1 + 1 / (2 * (D : ℝ))) * (q : ℝ) =
                (q : ℝ) + (q : ℝ) / (2 * (D : ℝ)) := by ring
          rw [hsplit] at hfactor
          norm_num at hKq
          linarith
        have hqK : q + K ≤ imax := by exact_mod_cast hqKreal
        exact False.elim (hfar hqK)
  refine ⟨hcount, ?_⟩
  exact lt_of_not_ge hfar

/-- A top-degree appearing atom with bounded maximum has every occupied source index in a fixed
two-sided window about the balanced scale. -/
theorem appearing_topDegree_support_window
    {n N D J q K : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hcount : ν.sum (fun _ k => k) = D)
    (hDqN : D * q ≤ N + J) (hNZ : magnitudeMaxXDegree Q < N)
    (hmax : ν.support.max'
      (appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ) < q + K)
    (hq : D * K + J + magnitudeMaxXDegree Q ≤ q) :
    ∀ i, ν i ≠ 0 →
      q - (D * K + J + magnitudeMaxXDegree Q) ≤ i ∧
        i ≤ q + (D * K + J + magnitudeMaxXDegree Q) := by
  let hsupp : ν.support.Nonempty :=
    appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ
  let imax := ν.support.max' hsupp
  have hmaxle : imax ≤ q + K := by
    change imax < q + K at hmax
    omega
  have hweight := (appearing_atom_weighted_sum_bounds Q hν).1
  have hsmallq : (D - 1) * K + J + magnitudeMaxXDegree Q ≤ q := by
    have hDK : (D - 1) * K ≤ D * K :=
      Nat.mul_le_mul_right K (Nat.sub_le D 1)
    omega
  have htail :
      q - ((D - 1) * K + J + magnitudeMaxXDegree Q) + (D - 1) * (q + K) ≤
        N - magnitudeMaxXDegree Q :=
    balanced_level_tail_ineq hD hsmallq hDqN hNZ.le
  have hlower := finsupp_tailSupport_of_count_weight_max hcount hweight hsupp hmaxle htail
  intro i hi
  have hiLower := hlower i hi
  have hiMax : i ≤ imax := Finset.le_max' ν.support i (Finsupp.mem_support_iff.mpr hi)
  have hLle : (D - 1) * K + J + magnitudeMaxXDegree Q ≤
      D * K + J + magnitudeMaxXDegree Q := by
    have hDK : (D - 1) * K ≤ D * K :=
      Nat.mul_le_mul_right K (Nat.sub_le D 1)
    omega
  constructor
  · exact (Nat.sub_le_sub_left hLle q).trans hiLower
  · have hKle : K ≤ D * K + J + magnitudeMaxXDegree Q := by
      have h1D : 1 ≤ D := by omega
      have : K ≤ D * K := by simpa [one_mul] using Nat.mul_le_mul_right K h1D
      omega
    exact hiMax.trans (hmaxle.trans (Nat.add_le_add_left hKle q))

/-- Once the coefficient level is linearly bounded by the balanced parameter, the logarithm of a
fixed polynomial mass majorant is bounded by its degree times `log(q+2)`. -/
theorem log_polynomial_mass_le_mul_log {A : ℝ} (hA : 0 ≤ A)
    {N q L E : ℕ} (hlevel : N + 1 ≤ L * (q + 1))
    (hlarge : A * (L : ℝ) ^ E + 1 ≤ (q : ℝ) + 2) :
    Real.log (A * (((N + 1) ^ E : ℕ) : ℝ) + 1) ≤
      ((E + 1 : ℕ) : ℝ) * Real.log ((q : ℝ) + 2) := by
  have hqpos : 0 < (q : ℝ) + 2 := by positivity
  have hpow1 : (1 : ℝ) ≤ ((q : ℝ) + 2) ^ E := one_le_pow₀ (by linarith)
  have hlevelR : (N : ℝ) + 1 ≤ (L : ℝ) * ((q : ℝ) + 1) := by
    exact_mod_cast hlevel
  have hlevelR' : (N : ℝ) + 1 ≤ (L : ℝ) * ((q : ℝ) + 2) := by
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  have hpoly : A * (((N + 1) ^ E : ℕ) : ℝ) + 1 ≤ ((q : ℝ) + 2) ^ (E + 1) := by
    push_cast
    calc
      A * ((N : ℝ) + 1) ^ E + 1
          ≤ A * ((L : ℝ) * ((q : ℝ) + 2)) ^ E + 1 := by
            gcongr
      _ = (A * (L : ℝ) ^ E) * ((q : ℝ) + 2) ^ E + 1 := by
            rw [mul_pow]
            ring
      _ ≤ (A * (L : ℝ) ^ E + 1) * ((q : ℝ) + 2) ^ E := by
            nlinarith
      _ ≤ ((q : ℝ) + 2) * ((q : ℝ) + 2) ^ E :=
            mul_le_mul_of_nonneg_right hlarge (pow_nonneg hqpos.le E)
      _ = ((q : ℝ) + 2) ^ (E + 1) := by rw [pow_succ']
  have hleftpos : 0 < A * (((N + 1) ^ E : ℕ) : ℝ) + 1 := by positivity
  calc
    Real.log (A * (((N + 1) ^ E : ℕ) : ℝ) + 1)
        ≤ Real.log (((q : ℝ) + 2) ^ (E + 1)) := Real.log_le_log hleftpos hpoly
    _ = ((E + 1 : ℕ) : ℝ) * Real.log ((q : ℝ) + 2) := by
      rw [Real.log_pow]

/-- A zero integer-normalized ADE coefficient has two distinct nonzero grouped atoms whose
valuations differ by at most the logarithm of the polynomial mass majorant. -/
theorem exists_near_min_nonzero_aevalWeight_of_relation
    {n N : ℕ} (F : PowerSeries ℂ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {b : ℕ → ℝ} (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    {νw : ℕ →₀ ℕ} (hνw : νw ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hww : aevalWeight n N Q νw ≠ 0) :
    let P : ℝ :=
      magnitudeCoefficientMass Q *
        (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
        (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ)
    ∃ ν₀ ν₁ : ℕ →₀ ℕ,
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 →
          ν₀.sum (fun i k => (k : ℝ) * b i) ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      ν₁ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₁ ≠ 0 ∧ ν₁ ≠ ν₀ ∧
      ν₁.sum (fun i k => (k : ℝ) * b i) <
        ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
  classical
  dsimp only
  obtain ⟨ν₀, hν₀, hw₀, hmin, _⟩ := exists_min_nonzero_aevalWeight Q b hνw hww
  let P : ℝ :=
    magnitudeCoefficientMass Q *
      (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
      (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ)
  have hP0 : 0 ≤ P := by
    have hcoeff0 : 0 ≤ magnitudeCoefficientMass Q := by
      rw [magnitudeCoefficientMass]
      positivity
    dsimp [P]
    exact mul_nonneg (mul_nonneg hcoeff0 (by positivity)) (by positivity)
  have hmassLe :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) ≤ P := by
    simpa only [P] using aevalWeight_mass_le_singlePolynomial n Q N
  have hmass :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp (Real.log (P + 1)) := by
    rw [Real.exp_log (by linarith : 0 < P + 1)]
    exact hmassLe.trans_lt (lt_add_one P)
  have hcoeffzero : PowerSeries.coeff N (aeval (formalJets n F) Q) = 0 := by
    rw [hrel, map_zero]
  have hex : ∃ ν₁ ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν₁ ≠ 0 ∧ ν₁ ≠ ν₀ ∧
      ν₁.sum (fun i k => (k : ℝ) * b i) <
        ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    by_contra hno
    push Not at hno
    have hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) ≤
            ν.sum (fun i k => (k : ℝ) * b i) := by
      intro ν hν hw hne
      exact hno ν hν hw hne
    have hne := aeval_coeff_ne_zero_of_int_dominant_on_support
      n N F Q hb hQint ν₀ hν₀ hw₀ hgap hmass
    exact hne hcoeffzero
  obtain ⟨ν₁, hν₁, hw₁, hne, hgap⟩ := hex
  exact ⟨ν₀, ν₁, hν₀, hw₀, hmin, hν₁, hw₁, hne, by simpa [P] using hgap⟩

/-- Every positive-degree integer-normalized ADE relation at a finite log-ratio greater than one
produces, at every sufficiently large balanced scale, two distinct fixed-window atoms whose
valuation defect is logarithmic. -/
theorem exists_eventually_logRatio_bend_pair_of_positiveJetDegree
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i) {lam : ℝ}
    (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ, 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
          ν₀.sum (fun i k => (k : ℝ) * b i) ∧
        ν₁.sum (fun i k => (k : ℝ) * b i) -
            ν₀.sum (fun i k => (k : ℝ) * b i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  classical
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  obtain ⟨anchor, ha, haD, _haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  have hDmax : D = magnitudeMaxJetDegree n Q := by simpa [D] using haD
  have hD : 0 < D := by rw [hDmax]; exact hDpos
  have haPos : 0 < jetMonomialDegree n anchor := by simpa [D] using hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  let J := jetMonomialOrder n anchor
  let Boff := magnitudeOffsetMax δ
  let E := D + O
  let C := E + 1
  let A : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hCoeffMass (by positivity)
  obtain ⟨r, R, hr1, hlamR, Nratio, hratio⟩ :=
    exists_eventually_geometric_ratio_bounds
      (Filter.Eventually.of_forall hbpos) hlam hlam1
  have hR1 : 1 < R := hlam1.trans hlamR
  have hratioLower : ∀ m ≥ Nratio, r ≤ b (m + 1) / b m := by
    intro m hm
    have h := (hratio m hm).2.1
    rw [le_div_iff₀ (hbpos m)]
    exact h
  have hratioUpper : ∀ m ≥ Nratio, b (m + 1) / b m ≤ R := by
    intro m hm
    have h := (hratio m hm).2.2
    rw [div_le_iff₀ (hbpos m)]
    exact h
  let Cval : ℝ := (D : ℝ) * R ^ Boff + 1
  have hpowT : Tendsto (fun k : ℕ => r ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr1
  obtain ⟨Kstep, hKstep⟩ : ∃ Kstep : ℕ, Cval < r ^ Kstep :=
    (hpowT.eventually_gt_atTop Cval).exists
  let K := D * Kstep + J + Z
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  obtain ⟨Qdom, hQdom⟩ := exists_const_mul_pow_lt_of_ratio_tendsto_gt_one
    (Filter.Eventually.of_forall hbpos) hlam hlam1 A hA Llevel E hLlevel
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      A * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (A * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  let Q₀ := max Qbal (max Qdom (max Qlarge
    (max Nratio (max (D * Kstep + J + Z)
      (max (2 * (J + Z) + 2) (2 * D * Kstep))))))
  refine ⟨D, K, C, Q₀, hD, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqdom : Qdom ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqratio : Nratio ≤ q := by
    dsimp [Q₀] at hq
    omega
  have hqK : D * Kstep + J + Z ≤ q := by
    dsimp [Q₀] at hq
    omega
  have hqthreshold : max (2 * (J + Z) + 2) (2 * D * Kstep) ≤ q := by
    dsimp [Q₀] at hq
    omega
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hqJ : J ≤ q := by omega
  have hqsum : q ≤ ∑ i, s i :=
    le_sum_of_le_apply haPos fun i => by simp [s]
  have hJsum : J ≤ (∑ i, s i) + anchor 0 :=
    hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hsLower : D * q ≤ ∑ i, s i :=
    mul_le_sum_of_le_apply fun i => by simp [s]
  have hDqN : D * q ≤ N + J := by rw [hNadd]; omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by
      have hbase : J + Z < D * Kstep + J + Z + 1 := by omega
      dsimp [Q₀] at hq
      omega
    have hqD : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    dsimp [Z]
    change magnitudeMaxXDegree Q < N
    omega
  obtain ⟨hνw, hww, _hgroup⟩ :
      key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q (key s) ≠ 0 ∧
        balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
          topShiftJetGroup n Q anchor := by
    simpa only [s, N, J] using hbalanced q hqbal
  let P : ℝ := A * (((N + 1) ^ E : ℕ) : ℝ)
  have hsUpper : (∑ i, s i) ≤ D * (q + Boff) :=
    sum_le_mul_of_apply_le fun i => by
      dsimp [s]
      exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
  have hNupper : N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := by
    dsimp [N]
    omega
  have hlevel : N + 1 ≤ Llevel * (q + 1) := by
    have hbaseNat : q + Boff ≤ (Boff + 1) * (q + 1) := by
      calc
        q + Boff ≤ q + Boff + (Boff * q + 1) := Nat.le_add_right _ _
        _ = (Boff + 1) * (q + 1) := by ring
    have hjet : D * (q + Boff) ≤ D * (Boff + 1) * (q + 1) := by
      calc
        D * (q + Boff) ≤ D * ((Boff + 1) * (q + 1)) :=
          Nat.mul_le_mul_left D hbaseNat
        _ = D * (Boff + 1) * (q + 1) := by ring
    have hconst : anchor 0 + 1 ≤ (anchor 0 + 1) * (q + 1) := by
      calc
        anchor 0 + 1 ≤ (anchor 0 + 1) + (anchor 0 + 1) * q := Nat.le_add_right _ _
        _ = (anchor 0 + 1) * (q + 1) := by ring
    calc
      N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := hNupper
      _ ≤ D * (Boff + 1) * (q + 1) + (anchor 0 + 1) * (q + 1) := by
        omega
      _ = Llevel * (q + 1) := by dsimp [Llevel]; ring
  have hPdom : P < b q := by
    have hpowLevel : (((N + 1) ^ E : ℕ) : ℝ) ≤
        (((Llevel * (q + 1)) ^ E : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_left hlevel E
    calc
      P ≤ A * (((Llevel * (q + 1)) ^ E : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hpowLevel hA.le
      _ < b q := hQdom q hqdom
  have hP0 : 0 < P := by
    dsimp [P]
    positivity
  have hlog : Real.log (P + 1) ≤ b q := by
    exact (Real.log_le_sub_one_of_pos (by linarith : 0 < P + 1)).trans
      (by simpa using hPdom.le)
  obtain ⟨ν₀, ν₁, hν₀, hw₀, hmin, hν₁, hw₁, hne, hgap⟩ :=
    exists_near_min_nonzero_aevalWeight_of_relation F Q hb hQint hrel hνw hww
  have hgapP : ν₁.sum (fun i k => (k : ℝ) * b i) <
      ν₀.sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    simpa [P, A, E, O, hDmax] using hgap
  have hlogpos : 0 < Real.log (P + 1) := Real.log_pos (by linarith)
  have hν₀near : ν₀.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) :=
    (hmin (key s) hνw hww).trans_lt (lt_add_of_pos_right _ hlogpos)
  have hν₁near : ν₁.sum (fun i k => (k : ℝ) * b i) <
      (key s).sum (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    exact hgapP.trans_le (add_le_add (hmin (key s) hνw hww) le_rfl)
  have hKraw : (D : ℝ) * R ^ magnitudeOffsetMax δ + 1 < r ^ Kstep := by
    simpa [Cval, Boff] using hKstep
  obtain ⟨hν₀count, hν₀max⟩ := near_balanced_atom_count_eq_and_supportMax_lt
    hbpos hr1 hR1 hratioLower hratioUpper Q hD hDmax δ hν₀
    (by simpa [s] using hν₀near) hlog hDqN (by simpa [Z] using hNZ) hqratio
    (by simpa [Z, J] using hqthreshold) hKraw
  obtain ⟨hν₁count, hν₁max⟩ := near_balanced_atom_count_eq_and_supportMax_lt
    hbpos hr1 hR1 hratioLower hratioUpper Q hD hDmax δ hν₁
    (by simpa [s] using hν₁near) hlog hDqN (by simpa [Z] using hNZ) hqratio
    (by simpa [Z, J] using hqthreshold) hKraw
  have hν₀window := appearing_topDegree_support_window Q hD hν₀ hν₀count hDqN
    (by simpa [Z] using hNZ) hν₀max (by simpa [K, Z, J] using hqK)
  have hν₁window := appearing_topDegree_support_window Q hD hν₁ hν₁count hDqN
    (by simpa [Z] using hNZ) hν₁max (by simpa [K, Z, J] using hqK)
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hA.le hlevel (hQlarge q hqlarge)
    simpa [P, C, A, E] using this
  have hdiff0 : 0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
      ν₀.sum (fun i k => (k : ℝ) * b i) := sub_nonneg.mpr (hmin ν₁ hν₁ hw₁)
  have hdiff : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) <
      (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * b i) -
        ν₀.sum (fun i k => (k : ℝ) * b i) < Real.log (P + 1) := by
      linarith [hgapP]
    exact this.trans_le hlogBound
  refine ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count, ?_, ?_, hdiff0, hdiff⟩
  · simpa [K] using hν₀window
  · simpa [K] using hν₁window

/-- Multiplicity pattern of an atom in the integer window `[q-K,q+K]`, truncated at the known
degree bound `D`. -/
def atomWindowPattern (q K D : ℕ) (ν : ℕ →₀ ℕ) :
    Fin (2 * K + 1) → Fin (D + 1) := fun j =>
  ⟨min (ν (q - K + (j : ℕ))) D, Nat.lt_succ_iff.mpr (min_le_right _ _)⟩

theorem atomWindowPattern_apply_of_le (q K D : ℕ) (ν : ℕ →₀ ℕ)
    (j : Fin (2 * K + 1)) (hν : ν (q - K + (j : ℕ)) ≤ D) :
    ((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) =
      ν (q - K + (j : ℕ)) := by
  simp [atomWindowPattern, min_eq_left hν]

/-- On atoms of degree `D` supported in `[q-K,q+K]`, the finite window pattern is injective. -/
theorem atomWindowPattern_injective_on_window {q K D : ℕ} (hq : K ≤ q)
    {ν μ : ℕ →₀ ℕ}
    (hνcount : ν.sum (fun _ k => k) = D)
    (hμcount : μ.sum (fun _ k => k) = D)
    (hνwin : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K)
    (hμwin : ∀ i, μ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K)
    (hpat : atomWindowPattern q K D ν = atomWindowPattern q K D μ) : ν = μ := by
  ext i
  have hνle : ∀ x, ν x ≤ D := fun x => (finsupp_apply_le_count ν x).trans hνcount.le
  have hμle : ∀ x, μ x ≤ D := fun x => (finsupp_apply_le_count μ x).trans hμcount.le
  have recover : ∀ {ξ : ℕ →₀ ℕ},
      (∀ x, ξ x ≤ D) → (∀ x, ξ x ≠ 0 → q - K ≤ x ∧ x ≤ q + K) →
      ∀ x, ξ x ≠ 0 → ∃ j : Fin (2 * K + 1), q - K + (j : ℕ) = x := by
    intro ξ hξle hξwin x hx
    obtain ⟨hxlo, hxhi⟩ := hξwin x hx
    have hwidth : x - (q - K) < 2 * K + 1 := by
      have hqsub : q - K + K = q := by omega
      omega
    exact ⟨⟨x - (q - K), hwidth⟩, Nat.add_sub_of_le hxlo⟩
  by_cases hνi : ν i = 0
  · by_cases hμi : μ i = 0
    · rw [hνi, hμi]
    · obtain ⟨j, hj⟩ := recover hμle hμwin i hμi
      have happ := congrArg Fin.val (congrFun hpat j)
      have hνdecode := atomWindowPattern_apply_of_le q K D ν j (hνle _)
      have hμdecode := atomWindowPattern_apply_of_le q K D μ j (hμle _)
      rw [hνdecode, hμdecode, hj, hνi] at happ
      exact (hμi happ.symm).elim
  · obtain ⟨j, hj⟩ := recover hνle hνwin i hνi
    have happ := congrArg Fin.val (congrFun hpat j)
    have hνdecode := atomWindowPattern_apply_of_le q K D ν j (hνle _)
    have hμdecode := atomWindowPattern_apply_of_le q K D μ j (hμle _)
    rw [hνdecode, hμdecode, hj] at happ
    exact happ

/-- The valuation of a window-supported atom is the finite dot product of its multiplicity
pattern with the translated log-magnitude window. -/
theorem valuation_eq_atomWindowPattern_sum {b : ℕ → ℝ} {q K D : ℕ} (hq : K ≤ q)
    {ν : ℕ →₀ ℕ} (hcount : ν.sum (fun _ k => k) = D)
    (hwin : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) :
    ν.sum (fun i k => (k : ℝ) * b i) =
      ∑ j : Fin (2 * K + 1),
        (((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) : ℝ) *
          b (q - K + (j : ℕ)) := by
  classical
  rw [Finsupp.sum]
  symm
  let idx : Fin (2 * K + 1) → ℕ := fun j => q - K + (j : ℕ)
  let active := Finset.univ.filter (fun j : Fin (2 * K + 1) => ν (idx j) ≠ 0)
  calc
    ∑ j : Fin (2 * K + 1),
        (((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) : ℝ) * b (idx j) =
      ∑ j ∈ active,
        (((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) : ℝ) * b (idx j) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro j hjuniv hjactive
        have hz : ν (idx j) = 0 := by
          simp only [active, Finset.mem_filter, Finset.mem_univ, true_and,
            not_not] at hjactive
          exact hjactive
        have hle : ν (idx j) ≤ D := (finsupp_apply_le_count ν _).trans hcount.le
        have happ := atomWindowPattern_apply_of_le q K D ν j hle
        rw [hz] at happ
        simp [happ]
    _ = ∑ i ∈ ν.support, (ν i : ℝ) * b i := by
      refine Finset.sum_bij'
        (fun j _ => idx j)
        (fun i hi =>
          (⟨i - (q - K), by
            have hi0 : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
            obtain ⟨hilo, hihi⟩ := hwin i hi0
            omega⟩ : Fin (2 * K + 1))) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        apply Finsupp.mem_support_iff.mpr
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      · intro i hi
        have hi0 : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, idx]
        obtain ⟨hilo, _hihi⟩ := hwin i hi0
        simpa [Nat.add_sub_of_le hilo] using hi0
      · intro j hj
        apply Fin.ext
        dsimp [idx]
        omega
      · intro i hi
        have hi0 : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
        obtain ⟨hilo, _hihi⟩ := hwin i hi0
        exact Nat.add_sub_of_le hilo
      · intro j hj
        have hle : ν (idx j) ≤ D := (finsupp_apply_le_count ν _).trans hcount.le
        rw [atomWindowPattern_apply_of_le q K D ν j hle]

theorem sum_atomWindowPattern_eq_count {q K D : ℕ} (hq : K ≤ q)
    {ν : ℕ →₀ ℕ} (hcount : ν.sum (fun _ k => k) = D)
    (hwin : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) :
    ∑ j : Fin (2 * K + 1),
      ((atomWindowPattern q K D ν j : Fin (D + 1)) : ℕ) = D := by
  have h := valuation_eq_atomWindowPattern_sum (b := fun _ => (1 : ℝ)) hq hcount hwin
  simp only [mul_one] at h
  have hcountR : ν.sum (fun _ k => (k : ℝ)) = (D : ℝ) := by
    simp only [Finsupp.sum]
    exact_mod_cast hcount
  rw [hcountR] at h
  exact_mod_cast h.symm

/-- Infinitely many bounded-window bend pairs contain one persistent ordered multiplicity
pattern.  Translating the window to start at zero produces a fixed integer shift combination
whose defect is nonnegative and logarithmic along a subsequence. -/
theorem exists_persistent_atomWindow_resonance
    {b : ℕ → ℝ} {D K C Q₀ : ℕ}
    (hpairs : ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * b i) -
          ν₀.sum (fun i k => (k : ℝ) * b i) ∧
        ν₁.sum (fun i k => (k : ℝ) * b i) -
            ν₀.sum (fun i k => (k : ℝ) * b i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2)) :
    ∃ p₀ p₁ : Fin (2 * K + 1) → Fin (D + 1),
      p₀ ≠ p₁ ∧
      (∑ j, (p₀ j : ℕ)) = D ∧ (∑ j, (p₁ j : ℕ)) = D ∧
      ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j : Fin (2 * K + 1),
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * b (q k + (j : ℕ)) ∧
        (∑ j : Fin (2 * K + 1),
          ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * b (q k + (j : ℕ))) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  classical
  let center : ℕ → ℕ := fun t => max Q₀ K + t
  let Good : ℕ → ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) → Prop := fun q ν =>
    ν.1 ≠ ν.2 ∧
      ν.1.sum (fun _ k => k) = D ∧ ν.2.sum (fun _ k => k) = D ∧
      (∀ i, ν.1 i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
      (∀ i, ν.2 i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
      0 ≤ ν.2.sum (fun i k => (k : ℝ) * b i) -
        ν.1.sum (fun i k => (k : ℝ) * b i) ∧
      ν.2.sum (fun i k => (k : ℝ) * b i) -
          ν.1.sum (fun i k => (k : ℝ) * b i) <
        (C : ℝ) * Real.log ((q : ℝ) + 2)
  have hex : ∀ t, ∃ ν, Good (center t) ν := by
    intro t
    obtain ⟨ν₀, ν₁, h⟩ := hpairs (center t) (by dsimp [center]; omega)
    exact ⟨(ν₀, ν₁), h⟩
  let chosen : ℕ → ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) := fun t => Classical.choose (hex t)
  have hchosen : ∀ t, Good (center t) (chosen t) := fun t => Classical.choose_spec (hex t)
  let patternPair : ℕ →
      (Fin (2 * K + 1) → Fin (D + 1)) × (Fin (2 * K + 1) → Fin (D + 1)) :=
    fun t =>
      (atomWindowPattern (center t) K D (chosen t).1,
        atomWindowPattern (center t) K D (chosen t).2)
  obtain ⟨p, hpInf⟩ := Finite.exists_infinite_fiber patternPair
  have hpSet : (patternPair ⁻¹' {p}).Infinite := Set.infinite_coe_iff.mp hpInf
  have hpUnbounded : ∀ N, ∃ t > N, patternPair t = p := by
    intro N
    obtain ⟨t, htmem, hNt⟩ := hpSet.exists_gt N
    exact ⟨t, hNt, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using htmem⟩
  obtain ⟨s, hsMono, hsPattern⟩ := Nat.exists_strictMono_subsequence hpUnbounded
  let q : ℕ → ℕ := fun k => center (s k) - K
  have hcenterK : ∀ t, K ≤ center t := by intro t; dsimp [center]; omega
  have hqTop : Tendsto q atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hsMono.tendsto_atTop
    exact Filter.Eventually.of_forall fun k => by dsimp [q, center]; omega
  have hpattern₀ : ∀ k,
      atomWindowPattern (center (s k)) K D (chosen (s k)).1 = p.1 := by
    intro k
    exact congrArg Prod.fst (hsPattern k)
  have hpattern₁ : ∀ k,
      atomWindowPattern (center (s k)) K D (chosen (s k)).2 = p.2 := by
    intro k
    exact congrArg Prod.snd (hsPattern k)
  have hpne : p.1 ≠ p.2 := by
    intro heq
    have hc := hchosen (s 0)
    exact hc.1 (atomWindowPattern_injective_on_window (hcenterK (s 0))
      hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
      ((hpattern₀ 0).trans (heq.trans (hpattern₁ 0).symm)))
  have hpsum₀ : (∑ j, (p.1 j : ℕ)) = D := by
    have hc := hchosen (s 0)
    rw [← hpattern₀ 0]
    exact sum_atomWindowPattern_eq_count (hcenterK (s 0)) hc.2.1 hc.2.2.2.1
  have hpsum₁ : (∑ j, (p.2 j : ℕ)) = D := by
    have hc := hchosen (s 0)
    rw [← hpattern₁ 0]
    exact sum_atomWindowPattern_eq_count (hcenterK (s 0)) hc.2.2.1 hc.2.2.2.2.1
  refine ⟨p.1, p.2, hpne, hpsum₀, hpsum₁, q, hqTop, fun k => ?_⟩
  have hc := hchosen (s k)
  have hv₀ := valuation_eq_atomWindowPattern_sum (b := b) (hcenterK (s k))
    hc.2.1 hc.2.2.2.1
  have hv₁ := valuation_eq_atomWindowPattern_sum (b := b) (hcenterK (s k))
    hc.2.2.1 hc.2.2.2.2.1
  have hcenter : center (s k) = q k + K :=
    (Nat.sub_add_cancel (hcenterK (s k))).symm
  have hdiff :
      (∑ j : Fin (2 * K + 1),
          ((((p.2 j : ℕ) : ℤ) - ((p.1 j : ℕ) : ℤ) : ℤ) : ℝ) *
            b (q k + (j : ℕ))) =
        (chosen (s k)).2.sum (fun i m => (m : ℝ) * b i) -
          (chosen (s k)).1.sum (fun i m => (m : ℝ) * b i) := by
    rw [hv₀, hv₁]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hidx : center (s k) - K + (j : ℕ) = q k + (j : ℕ) := rfl
    rw [hidx, hpattern₀ k, hpattern₁ k]
    push_cast
    ring
  constructor
  · rw [hdiff]
    exact hc.2.2.2.2.2.1
  · rw [hdiff]
    simpa only [hcenter] using hc.2.2.2.2.2.2

/-- Integer polynomial recording the difference of two finite multiplicity patterns. -/
def atomPatternDifferencePolynomial {M D : ℕ}
    (p₀ p₁ : Fin M → Fin (D + 1)) : Polynomial ℤ :=
  ∑ j : Fin M,
    Polynomial.monomial (j : ℕ) (((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ))

theorem atomPatternDifferencePolynomial_coeff {M D : ℕ}
    (p₀ p₁ : Fin M → Fin (D + 1)) (r : ℕ) :
    (atomPatternDifferencePolynomial p₀ p₁).coeff r =
      if h : r < M then ((p₁ ⟨r, h⟩ : ℕ) : ℤ) - ((p₀ ⟨r, h⟩ : ℕ) : ℤ) else 0 := by
  classical
  rw [atomPatternDifferencePolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs with hr
  · rw [Finset.sum_eq_single ⟨r, hr⟩]
    · simp
    · intro j hj hne
      simp only [ite_eq_right_iff]
      intro hjr
      exact (hne (Fin.ext hjr)).elim
    · simp
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [ite_eq_right_iff]
    intro hjr
    exact (hr (hjr ▸ j.isLt)).elim

theorem atomPatternDifferencePolynomial_ne_zero {M D : ℕ}
    {p₀ p₁ : Fin M → Fin (D + 1)} (hne : p₀ ≠ p₁) :
    atomPatternDifferencePolynomial p₀ p₁ ≠ 0 := by
  classical
  intro hzero
  apply hne
  funext j
  have hc : (atomPatternDifferencePolynomial p₀ p₁).coeff (j : ℕ) = 0 := by
    rw [hzero]
    simp
  rw [atomPatternDifferencePolynomial_coeff, dif_pos j.isLt] at hc
  apply Fin.ext
  exact Int.ofNat_inj.mp (sub_eq_zero.mp hc).symm

/-- Equal total multiplicity gives the persistent difference polynomial the root `1`. -/
theorem atomPatternDifferencePolynomial_eval_one {M D : ℕ}
    (p₀ p₁ : Fin M → Fin (D + 1))
    (hsum : (∑ j, (p₀ j : ℕ)) = ∑ j, (p₁ j : ℕ)) :
    (atomPatternDifferencePolynomial p₀ p₁).eval 1 = 0 := by
  classical
  simp only [atomPatternDifferencePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]
  rw [Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact_mod_cast hsum.symm

/-- A logarithmic window defect is negligible compared with a positive sequence whose finite
successive-ratio limit is greater than one. -/
theorem tendsto_log_shift_div_of_ratio_tendsto_gt_one
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i) {lam : ℝ}
    (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (C K : ℕ) :
    Tendsto (fun k =>
      (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) / b (q k))
      atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun k => ((q k + K : ℕ) : ℝ) + 2
  have hqR : Tendsto (fun k => (q k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hx : Tendsto x atTop atTop := by
    have hadd : Tendsto (fun k => (q k : ℝ) + ((K : ℝ) + 2)) atTop atTop :=
      hqR.atTop_add tendsto_const_nhds
    simpa only [x, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hadd
  have hlogx : Tendsto (fun k => Real.log (x k) / x k) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hx).tendsto_div_nhds_zero
  have hinvq : Tendsto (fun k => ((q k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hqR
  have hxqForm : Tendsto (fun k => (1 : ℝ) + ((K : ℝ) + 2) * (q k : ℝ)⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hinvq.const_mul ((K : ℝ) + 2))
  have hxq : Tendsto (fun k => x k / (q k : ℝ)) atTop (𝓝 1) := by
    refine hxqForm.congr' ?_
    filter_upwards [hq.eventually_gt_atTop 0] with k hk
    have hq0 : (q k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    dsimp [x]
    push_cast
    field_simp
    ring
  have hlogq : Tendsto (fun k => Real.log (x k) / (q k : ℝ)) atTop (𝓝 0) := by
    have hmul := hlogx.mul hxq
    simp only [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards with k
    have hx0 : x k ≠ 0 := by dsimp [x]; positivity
    field_simp
  have hnum : Tendsto (fun k =>
      (C : ℝ) * Real.log (x k) / (q k : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hlogq.const_mul (C : ℝ)
  have hden : Tendsto (fun k => b (q k) / (q k : ℝ)) atTop atTop :=
    (tendsto_div_natCast_atTop_of_ratio_tendsto_gt_one
      (Filter.Eventually.of_forall hbpos) hlam hlam1).comp hq
  have hquot := hnum.div_atTop hden
  refine hquot.congr' ?_
  filter_upwards [hq.eventually_gt_atTop 0] with k hk
  have hq0 : (q k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  dsimp [x]
  field_simp

/-- The canonical `natDegree` sum of a pattern-difference polynomial is exactly its finite
window dot product. -/
theorem sum_range_atomPatternDifferencePolynomial {M D : ℕ} (hM : 0 < M)
    (p₀ p₁ : Fin M → Fin (D + 1)) (b : ℕ → ℝ) (q : ℕ) :
    (∑ r ∈ Finset.range ((atomPatternDifferencePolynomial p₀ p₁).natDegree + 1),
      ((atomPatternDifferencePolynomial p₀ p₁).coeff r : ℝ) * b (q + r)) =
    ∑ j : Fin M,
      ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * b (q + (j : ℕ)) := by
  classical
  let Q := atomPatternDifferencePolynomial p₀ p₁
  have hdeg : Q.natDegree < M := by
    have hle : Q.natDegree ≤ M - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [atomPatternDifferencePolynomial_coeff]
      rw [dif_neg (by omega)]
    omega
  have hsub : Finset.range (Q.natDegree + 1) ⊆ Finset.range M :=
    Finset.range_mono (by omega)
  change (∑ r ∈ Finset.range (Q.natDegree + 1), (Q.coeff r : ℝ) * b (q + r)) = _
  calc
    (∑ r ∈ Finset.range (Q.natDegree + 1), (Q.coeff r : ℝ) * b (q + r)) =
        ∑ r ∈ Finset.range M, (Q.coeff r : ℝ) * b (q + r) := by
      refine Finset.sum_subset hsub ?_
      intro r hrM hrSmall
      have hnr : Q.natDegree < r := by
        simp only [Finset.mem_range, not_lt] at hrSmall
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hnr]
      simp
    _ = ∑ j : Fin M,
        ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * b (q + (j : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun r => (Q.coeff r : ℝ) * b (q + r)) M]
      apply Finset.sum_congr rfl
      intro j hj
      rw [atomPatternDifferencePolynomial_coeff, dif_pos j.isLt]

/-- **DA log-ratio resonance law, positive-degree relation form.**  An integer-normalized
algebraic differential relation of positive jet degree for a full-support coefficient sequence
with finite log-ratio limit `lam > 1` produces a nonzero integer polynomial vanishing at both
`1` and `lam`. -/
theorem exists_logRatio_resonancePolynomial_of_positiveJetDegree_relation
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i) {lam : ℝ}
    (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (R : MvPolynomial (Fin (n + 2)) ℂ)
    (hRint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m R = (z : ℂ))
    (hrel : aeval (formalJets n F) R = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n R) :
    ∃ Q : Polynomial ℤ, Q ≠ 0 ∧ Q.eval 1 = 0 ∧ (Polynomial.aeval lam) Q = 0 := by
  classical
  obtain ⟨D, K, C, Q₀, hD, hC, hpairs⟩ :=
    exists_eventually_logRatio_bend_pair_of_positiveJetDegree
      hbpos hlam hlam1 F hb R hRint hrel hDpos
  obtain ⟨p₀, p₁, hpne, hsum₀, hsum₁, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_resonance hpairs
  let Q : Polynomial ℤ := atomPatternDifferencePolynomial p₀ p₁
  have hQ : Q ≠ 0 := atomPatternDifferencePolynomial_ne_zero hpne
  have hQone : Q.eval 1 = 0 :=
    atomPatternDifferencePolynomial_eval_one p₀ p₁ (hsum₀.trans hsum₁.symm)
  let S : ℕ → ℝ := fun k => ∑ j : Fin (2 * K + 1),
    ((((p₁ j : ℕ) : ℤ) - ((p₀ j : ℕ) : ℤ) : ℤ) : ℝ) * b (q k + (j : ℕ))
  have hupper : Tendsto (fun k =>
      (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) / b (q k))
      atTop (𝓝 0) :=
    tendsto_log_shift_div_of_ratio_tendsto_gt_one hbpos hlam hlam1 hq C K
  have hS : Tendsto (fun k => S k / b (q k)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => div_nonneg (hdefect k).1 (hbpos (q k)).le)
      (fun k => ?_) hupper
    exact div_le_div_of_nonneg_right (hdefect k).2.le (hbpos (q k)).le
  have hres : Tendsto (fun k =>
      (∑ r ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff r : ℝ) * b (q k + r)) / b (q k)) atTop (𝓝 0) := by
    refine hS.congr' (Filter.Eventually.of_forall fun k => ?_)
    dsimp [S, Q]
    rw [sum_range_atomPatternDifferencePolynomial (by omega)]
  have hroot : (Polynomial.aeval lam) Q = 0 :=
    logRatio_resonance_aeval_eq_zero
      (Filter.Eventually.of_forall fun i => (hbpos i).ne') hlam Q hq hres
  exact ⟨Q, hQ, hQone, hroot⟩

theorem logRatio_isAlgebraic_of_positiveJetDegree_relation
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i) {lam : ℝ}
    (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (R : MvPolynomial (Fin (n + 2)) ℂ)
    (hRint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m R = (z : ℂ))
    (hrel : aeval (formalJets n F) R = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n R) :
    IsAlgebraic ℤ lam := by
  obtain ⟨Q, hQ, _hQone, hroot⟩ :=
    exists_logRatio_resonancePolynomial_of_positiveJetDegree_relation
      hbpos hlam hlam1 F hb R hRint hrel hDpos
  exact ⟨Q, hQ, hroot⟩

/-- A nonzero integer-normalized formal relation for a full-support coefficient sequence cannot
have jet degree zero: in that case its unique zero atom is automatically dominant, contradicting
the vanishing relation. -/
theorem magnitudeMaxJetDegree_pos_of_integer_relation
    {b : ℕ → ℝ} {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i))
    (R : MvPolynomial (Fin (n + 2)) ℂ) (hR : R ≠ 0)
    (hRint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m R = (z : ℂ))
    (hrel : aeval (formalJets n F) R = 0) :
    0 < magnitudeMaxJetDegree n R := by
  rcases Nat.eq_zero_or_pos (magnitudeMaxJetDegree n R) with hzero | hpos
  · obtain ⟨N, ν₀, G, hν₀, hw₀, hgap, hmass⟩ :=
      exists_intDominance_of_zeroJetDegree (b := b) R hR hzero
    have hne := aeval_coeff_ne_zero_of_int_dominant_on_support
      n N F R hb hRint ν₀ hν₀ hw₀ hgap hmass
    rw [hrel, map_zero] at hne
    exact False.elim (hne rfl)
  · exact hpos

/-- **Unconditional analytic DA log-ratio law.**  A smooth differentially algebraic function with
full-support Taylor magnitudes `exp (-b n)` and finite successive log-ratio limit `lam > 1`
produces one nonzero integer resonance polynomial satisfying `Q(1)=Q(lam)=0`. -/
theorem exists_logRatio_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, Q ≠ 0 ∧ Q.eval 1 = 0 ∧ (Polynomial.aeval lam) Q = 0 := by
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', R, hR, hRint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb R hR hRint hrel
  exact exists_logRatio_resonancePolynomial_of_positiveJetDegree_relation
    hbpos hlam hlam1 (taylorPS f) hb R hRint hrel hDpos

theorem logRatio_isAlgebraic_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hDA : DifferentiallyAlgebraic f) :
    IsAlgebraic ℤ lam := by
  obtain ⟨Q, hQ, _hQone, hroot⟩ :=
    exists_logRatio_resonancePolynomial_of_differentiallyAlgebraic
      hf hbpos hb hlam hlam1 hDA
  exact ⟨Q, hQ, hroot⟩

/-- A transcendental finite Taylor log-ratio greater than one forces hypertranscendence. -/
theorem hypertranscendental_of_transcendental_logRatio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hlamTrans : Transcendental ℚ lam) :
    Hypertranscendental f := by
  intro hDA
  have hz : IsAlgebraic ℤ lam :=
    logRatio_isAlgebraic_of_differentiallyAlgebraic hf hbpos hb hlam hlam1 hDA
  obtain ⟨Q, hQ, hroot⟩ := hz
  have hq : IsAlgebraic ℚ lam := by
    refine ⟨Q.map (algebraMap ℤ ℚ), ?_, ?_⟩
    · exact fun hc => hQ ((Polynomial.map_eq_zero_iff
        (algebraMap ℤ ℚ).injective_int).mp hc)
    · rw [Polynomial.aeval_map_algebraMap]
      exact hroot
  exact hlamTrans hq

/-- The finite Taylor prefix is irrelevant to the finite DA log-ratio algebraicity law. -/
theorem logRatio_isAlgebraic_of_eventually_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hDA : DifferentiallyAlgebraic f) :
    IsAlgebraic ℤ lam := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hb.and hbpos)
  let F := taylorPS f
  let p := finiteTaylorCorrection F T
  let g : ℂ → ℂ := fun z => f z + p.eval z
  let b' : ℕ → ℝ := fun i => if i < T then 1 else b i
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ = Real.exp (-b' i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe, coeff_finiteTaylorCorrection]
    by_cases hi : i < T
    · simp [b', hi, Complex.norm_exp]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      rw [show b' i = b i by simp [b', hi]]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-b i)
      simpa only [F] using (hT i hiT).1
  have hb'pos : ∀ i, 0 < b' i := by
    intro i
    by_cases hi : i < T
    · simp [b', hi]
    · simpa [b', hi] using (hT i (Nat.le_of_not_gt hi)).2
  have hratio' : Tendsto (fun i => b' (i + 1) / b' i) atTop (𝓝 lam) := by
    refine hlam.congr' ?_
    filter_upwards [eventually_ge_atTop T] with i hi
    have hi0 : ¬ i < T := Nat.not_lt.mpr hi
    have hi1 : ¬ i + 1 < T := Nat.not_lt.mpr (hi.trans (Nat.le_add_right i 1))
    simp [b', hi0, hi1]
  have hgDA : DifferentiallyAlgebraic g :=
    DifferentiallyAlgebraic.add_polynomial hDA hf p
  exact logRatio_isAlgebraic_of_differentiallyAlgebraic
    hgsm hb'pos hb' hratio' hlam1 hgDA

/-- **Paper-form corollary.**  Eventual full Taylor support with a finite transcendental
successive log-magnitude ratio greater than one forces hypertranscendence. -/
theorem hypertranscendental_of_eventually_transcendental_logRatio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hlamTrans : Transcendental ℚ lam) :
    Hypertranscendental f := by
  intro hDA
  have hz : IsAlgebraic ℤ lam :=
    logRatio_isAlgebraic_of_eventually_differentiallyAlgebraic
      hf hb hbpos hlam hlam1 hDA
  obtain ⟨Q, hQ, hroot⟩ := hz
  apply hlamTrans
  refine ⟨Q.map (algebraMap ℤ ℚ), ?_, ?_⟩
  · exact fun hc => hQ ((Polynomial.map_eq_zero_iff
      (algebraMap ℤ ℚ).injective_int).mp hc)
  · rw [Polynomial.aeval_map_algebraMap]
    exact hroot

/-- Direct logarithmic-magnitude formulation of the transcendental finite-ratio criterion. -/
theorem hypertranscendental_of_eventually_transcendental_taylorLogRatio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hne : ∀ᶠ i in atTop, PowerSeries.coeff i (taylorPS f) ≠ 0)
    (hbpos : ∀ᶠ i in atTop,
      0 < -Real.log ‖PowerSeries.coeff i (taylorPS f)‖)
    {lam : ℝ}
    (hlam : Tendsto (fun i =>
      (-Real.log ‖PowerSeries.coeff (i + 1) (taylorPS f)‖) /
        (-Real.log ‖PowerSeries.coeff i (taylorPS f)‖)) atTop (𝓝 lam))
    (hlam1 : 1 < lam) (hlamTrans : Transcendental ℚ lam) :
    Hypertranscendental f := by
  let b : ℕ → ℝ := fun i => -Real.log ‖PowerSeries.coeff i (taylorPS f)‖
  apply hypertranscendental_of_eventually_transcendental_logRatio
    (b := b) hf
  · filter_upwards [hne] with i hi
    have hnorm : 0 < ‖PowerSeries.coeff i (taylorPS f)‖ := norm_pos_iff.mpr hi
    dsimp [b]
    rw [neg_neg, Real.exp_log hnorm]
  · simpa only [b] using hbpos
  · simpa only [b] using hlam
  · exact hlam1
  · exact hlamTrans

/-- Finite extended-spectrum statement: a DA series whose finite log-ratio limit is at least one
has limit `1`, or an algebraic limit strictly greater than `1`. -/
theorem differentiallyAlgebraic_logRatio_finiteSpectrum
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    {lam : ℝ} (hlam : Tendsto (fun i => b (i + 1) / b i) atTop (𝓝 lam))
    (hlam_ge_one : 1 ≤ lam) (hDA : DifferentiallyAlgebraic f) :
    lam = 1 ∨ (1 < lam ∧ IsAlgebraic ℤ lam) := by
  rcases hlam_ge_one.eq_or_lt with hEq | hlt
  · exact Or.inl hEq.symm
  · exact Or.inr ⟨hlt,
      logRatio_isAlgebraic_of_eventually_differentiallyAlgebraic
        hf hb hbpos hlam hlt hDA⟩

/-- Infinite log-ratio is excluded from the DA spectrum by the existing log-superlacunary
hypertranscendence theorem. -/
theorem differentiallyAlgebraic_logRatio_not_tendsto_atTop
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    (hDA : DifferentiallyAlgebraic f) :
    ¬ Tendsto (fun i => b (i + 1) / b i) atTop atTop := by
  intro htop
  exact (hypertranscendental_of_eventually_logSuperlacunary hf hb hbpos htop) hDA

end

end GaloisForLFunctions
