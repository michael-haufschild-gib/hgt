import GaloisForLFunctions.BiScaleUncertainty.HyperbolicMultiplierGramTransfer
import GaloisForLFunctions.RHTower.EvenSectorSmoothBlindInterpolationObstruction

/-!
# A smooth odd logarithmic-zero family with exact multiplier leakage

Six separated translates cancel the source correlation at `log 2`, while their
sine-multiplied correlations have a positive weighted overlap. The source energy
stays fixed as the packets move away from the origin. The exact leakage law, not
an assumed inherited clique, is the positive invariant of this construction.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported ContDiff

namespace GaloisForLFunctions.BiScaleUncertainty.OddMultiplierLeakage
open RHTower.ArchimedeanAnomaly
open _root_.RHTower.EvenSector _root_.RHTower.EvenSector.SmoothBlindInterpolation
open _root_.RHTower.AutocorrelationKrein _root_.RHTower.SeparatedBump
noncomputable section

def lag : ℝ := Real.log 2

theorem lag_pos : 0 < lag := Real.log_pos (by norm_num)

private theorem width_lt_lag : pulseWidth < lag := by
  unfold pulseWidth lag
  linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

private theorem packet_even (u : ℝ) : packet (-u) = packet u := evenPolarProfile_neg 20 u

private theorem packet_support (u : ℝ) (hu : pulseWidth / 2 < |u|) : packet u = 0 :=
  evenPolarProfile_eq_zero 20 (by linarith [packet_diameter_lt])

def node (T : ℝ) : Fin 6 → ℝ :=
  ![|T| + lag, |T| + 2 * lag, |T| + 3 * lag,
    -(|T| + lag), -(|T| + 2 * lag), -(|T| + 3 * lag)]

def coefficient : Fin 6 → ℝ := ![-1, 1, 1, 1, -1, -1]

private theorem sum_fin_six (g : Fin 6 → ℝ) :
    ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change g 0 + (g 1 + (g 2 + (g 3 + (g 4 + g 5)))) = _
  ring

def sourceFn (T u : ℝ) : ℝ := ∑ i : Fin 6, coefficient i * packet (u - node T i)

theorem sourceFn_smooth (T : ℝ) : ContDiff ℝ ∞ (sourceFn T) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (packet_smooth.comp (contDiff_id.sub contDiff_const))

theorem sourceFn_compact (T : ℝ) : HasCompactSupport (sourceFn T) := by
  apply hasCompactSupport_finset_sum
  intro i _
  exact (packet_compact.comp_homeomorph (Homeomorph.subRight (node T i))).mul_left

def source (T : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨sourceFn T, (sourceFn_smooth T).continuous⟩, sourceFn_compact T⟩

theorem source_odd (T u : ℝ) : source T (-u) = -source T u := by
  have hp (a : ℝ) : packet (-u - a) = packet (u + a) := by
    rw [show -u - a = -(u + a) by ring, packet_even]
  change sourceFn T (-u) = -sourceFn T u
  simp [sourceFn, Fin.sum_univ_succ, coefficient, node, hp]
  ring_nf

private def adjacent (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 4)

private theorem adjacent_node (T : ℝ) (i j : Fin 6) (h : adjacent i j) :
    node T j = node T i + lag := by
  rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp [node] <;> ring

private theorem node_gap (T : ℝ) (i j : Fin 6) (h : i ≠ j) :
    lag ≤ |node T i - node T j| := by
  have ht := abs_nonneg T
  have hd := lag_pos
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [Fin.ext_iff] at h
  all_goals norm_num [node]
  all_goals
    by_contra hn
    have hh := abs_lt.mp (lt_of_not_ge hn)
    rcases hh with ⟨ha, hb⟩
    linarith

private theorem node_lag_gap (T : ℝ) (i j : Fin 6) (h : ¬adjacent i j) :
    lag ≤ |node T i + lag - node T j| := by
  have ht := abs_nonneg T
  have hd := lag_pos
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [adjacent, Fin.ext_iff] at h
  all_goals norm_num [node]
  all_goals try linarith [le_abs_self lag]
  all_goals
    by_contra hn
    have hh := abs_lt.mp (lt_of_not_ge hn)
    rcases hh with ⟨ha, hb⟩
    linarith

private theorem packet_pair_zero (a b x : ℝ) (hg : lag ≤ |a + x - b|) (u : ℝ) :
    packet (u - a) * packet (u + x - b) = 0 := by
  have hs : pulseWidth < |a - (b - x)| := by
    rw [show a - (b - x) = a + x - b by ring]
    exact width_lt_lag.trans_le hg
  have h := mul_translate_eq_zero packet_support hs u
  simpa only [show u - (b - x) = u + x - b by ring] using h

private def weightedOverlap (w : C(ℝ, ℝ)) (a b x : ℝ) : ℝ :=
  ∫ u, w u * w (u + x) * packet (u - a) * packet (u + x - b)

private def weightedDiagonal (w : C(ℝ, ℝ)) (a x : ℝ) : ℝ :=
  ∫ u, w (u + a) * w (u + a + x) * packet u ^ 2

private theorem integrable_weightedOverlap (w : C(ℝ, ℝ)) (a b x : ℝ) :
    Integrable (fun u => w u * w (u + x) * packet (u - a) * packet (u + x - b)) := by
  have hs : HasCompactSupport (fun u => packet (u - a)) :=
    packet_compact.comp_homeomorph (Homeomorph.subRight a)
  have hc := packet_smooth.continuous
  exact (by fun_prop : Continuous fun u => w u * w (u + x) * packet (u - a) *
    packet (u + x - b)).integrable_of_hasCompactSupport hs.mul_left.mul_right

private theorem weightedOverlap_zero (w : C(ℝ, ℝ)) (a b x : ℝ)
    (hg : lag ≤ |a + x - b|) : weightedOverlap w a b x = 0 := by
  unfold weightedOverlap
  have he (u : ℝ) : w u * w (u + x) * packet (u - a) * packet (u + x - b) = 0 := by
    calc
      _ = (w u * w (u + x)) * (packet (u - a) * packet (u + x - b)) := by ring
      _ = 0 := by rw [packet_pair_zero a b x hg, mul_zero]
  simp_rw [he]
  exact integral_zero _ _

private theorem weightedOverlap_diagonal (w : C(ℝ, ℝ)) (a x : ℝ) :
    weightedOverlap w a (a + x) x = weightedDiagonal w a x := by
  unfold weightedOverlap weightedDiagonal
  have h := integral_add_right_eq_self (μ := volume)
    (fun u => w u * w (u + x) * packet (u - a) ^ 2) a
  simp only [add_sub_cancel_right] at h
  calc
    _ = ∫ u, w u * w (u + x) * packet (u - a) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [show u + x - (a + x) = u - a by ring]
      ring
    _ = _ := h.symm

private theorem autocorr_weighted_source (T : ℝ) (w : C(ℝ, ℝ)) (x : ℝ) :
    autocorr (fun u => w u * source T u) x =
      ∑ i : Fin 6, ∑ j : Fin 6,
        coefficient i * coefficient j * weightedOverlap w (node T i) (node T j) x := by
  have hi (i j : Fin 6) : Integrable (fun u => coefficient i * coefficient j *
      (w u * w (u + x) * packet (u - node T i) * packet (u + x - node T j))) :=
    (integrable_weightedOverlap w _ _ _).const_mul _
  have he : (fun u => (w u * source T u) * (w (u + x) * source T (u + x))) =
      fun u => ∑ i : Fin 6, ∑ j : Fin 6, coefficient i * coefficient j *
        (w u * w (u + x) * packet (u - node T i) * packet (u + x - node T j)) := by
    funext u
    change (w u * ∑ i : Fin 6, coefficient i * packet (u - node T i)) *
      (w (u + x) * ∑ j : Fin 6, coefficient j * packet (u + x - node T j)) = _
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold autocorr
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  exact integral_const_mul _ _

private theorem autocorr_weighted_source_lag (T : ℝ) (w : C(ℝ, ℝ)) :
    autocorr (fun u => w u * source T u) lag =
      -weightedDiagonal w (|T| + lag) lag + weightedDiagonal w (|T| + 2 * lag) lag -
        weightedDiagonal w (-(|T| + 2 * lag)) lag +
        weightedDiagonal w (-(|T| + 3 * lag)) lag := by
  classical
  rw [autocorr_weighted_source]
  have he (i j : Fin 6) : weightedOverlap w (node T i) (node T j) lag =
      if adjacent i j then weightedDiagonal w (node T i) lag else 0 := by
    by_cases h : adjacent i j
    · rw [if_pos h, adjacent_node T i j h, weightedOverlap_diagonal]
    · rw [if_neg h]
      exact weightedOverlap_zero w _ _ _ (node_lag_gap T i j h)
  simp_rw [he]
  simp only [sum_fin_six]
  dsimp [coefficient, node]
  norm_num [coefficient, node, adjacent, Fin.ext_iff]
  ring

private def oneWeight : C(ℝ, ℝ) := ⟨fun _ => 1, continuous_const⟩

private def sineWeight : C(ℝ, ℝ) := ⟨fun u => Real.sinh (u / 2), by fun_prop⟩

private theorem weightedDiagonal_one (a x : ℝ) : weightedDiagonal oneWeight a x = packetMass := by
  change (∫ u, (1 : ℝ) * 1 * packet u ^ 2) = autocorr packet 0
  simpa only [one_mul] using integral_sq_eq_autocorr_zero packet

/-- Every member has the same positive original energy, regardless of packet position. -/
theorem source_autocorr_zero (T : ℝ) : autocorr (source T) 0 = 6 * packetMass := by
  classical
  have he (i j : Fin 6) : weightedOverlap oneWeight (node T i) (node T j) 0 =
      if i = j then packetMass else 0 := by
    by_cases h : i = j
    · subst j
      simpa only [add_zero, weightedDiagonal_one, if_true] using
        weightedOverlap_diagonal oneWeight (node T i) 0
    · rw [if_neg h]
      apply weightedOverlap_zero
      simpa only [add_zero] using node_gap T i j h
  calc
    _ = ∑ i : Fin 6, ∑ j : Fin 6,
        coefficient i * coefficient j * weightedOverlap oneWeight (node T i) (node T j) 0 := by
      simpa [oneWeight] using autocorr_weighted_source T oneWeight 0
    _ = _ := by
      simp_rw [he]
      simp only [sum_fin_six]
      dsimp [coefficient]
      norm_num [coefficient, Fin.ext_iff]
      ring

theorem source_energy_pos (T : ℝ) : 0 < autocorr (source T) 0 := by
  rw [source_autocorr_zero]
  exact mul_pos (by norm_num) packetMass_pos

/-- Exact blindness at the actual logarithmic node `log 2`. -/
theorem source_autocorr_lag (T : ℝ) : autocorr (source T) lag = 0 := by
  have h := autocorr_weighted_source_lag T oneWeight
  simp only [weightedDiagonal_one] at h
  simpa [oneWeight] using h

/-- The positive weighted packet invariant governing the multiplier leakage. -/
def packetCoshMass : ℝ := ∫ u, Real.cosh u * packet u ^ 2

private theorem integrable_packet_sq : Integrable (fun u => packet u ^ 2) := by
  have hs : HasCompactSupport (fun u => packet u * packet u) := packet_compact.mul_left
  have hs' : HasCompactSupport (fun u => packet u ^ 2) := by simpa only [sq] using hs
  have hc := packet_smooth.continuous
  exact (by fun_prop : Continuous (fun u => packet u ^ 2)).integrable_of_hasCompactSupport hs'

private theorem integrable_packet_weight (w : C(ℝ, ℝ)) :
    Integrable (fun u => w u * packet u ^ 2) := by
  have hs : HasCompactSupport (fun u => packet u * packet u) := packet_compact.mul_left
  have hs' : HasCompactSupport (fun u => packet u ^ 2) := by simpa only [sq] using hs
  exact (w.continuous.mul (packet_smooth.continuous.pow 2)).integrable_of_hasCompactSupport hs'.mul_left

theorem packetMass_le_packetCoshMass : packetMass ≤ packetCoshMass := by
  have h := integral_mono integrable_packet_sq
    (integrable_packet_weight ⟨Real.cosh, Real.continuous_cosh⟩) (fun u => ?_)
  · simpa only [packetMass, packetCoshMass, ContinuousMap.coe_mk,
      integral_sq_eq_autocorr_zero] using h
  · change packet u ^ 2 ≤ Real.cosh u * packet u ^ 2
    nlinarith [Real.one_le_cosh u, sq_nonneg (packet u)]

theorem packetCoshMass_pos : 0 < packetCoshMass :=
  packetMass_pos.trans_le packetMass_le_packetCoshMass

private theorem packet_sinh_integral_zero : (∫ u, Real.sinh u * packet u ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun u => Real.sinh u * packet u ^ 2) volume
  simp only [Real.sinh_neg, packet_even, neg_mul, integral_neg] at h
  linarith

private theorem packet_cosh_shift_integral (a : ℝ) :
    (∫ u, Real.cosh (u + a) * packet u ^ 2) = Real.cosh a * packetCoshMass := by
  have hc : Integrable (fun u => Real.cosh a * (Real.cosh u * packet u ^ 2)) :=
    (integrable_packet_weight ⟨Real.cosh, Real.continuous_cosh⟩).const_mul _
  have hs : Integrable (fun u => Real.sinh a * (Real.sinh u * packet u ^ 2)) :=
    (integrable_packet_weight ⟨Real.sinh, Real.continuous_sinh⟩).const_mul _
  have he : (fun u => Real.cosh (u + a) * packet u ^ 2) =
      fun u => Real.cosh a * (Real.cosh u * packet u ^ 2) +
        Real.sinh a * (Real.sinh u * packet u ^ 2) := by
    funext u
    rw [Real.cosh_add]
    ring
  rw [he, integral_add hc hs, integral_const_mul, integral_const_mul,
    packet_sinh_integral_zero, mul_zero, add_zero]
  rfl

private def sinePacketPair (a b : ℝ) : ℝ :=
  ∫ u, Real.sinh ((u + a) / 2) * Real.sinh ((u + b) / 2) * packet u ^ 2

private theorem sinePacketPair_eq (a b : ℝ) :
    sinePacketPair a b = (Real.cosh ((a + b) / 2) * packetCoshMass -
      Real.cosh ((a - b) / 2) * packetMass) / 2 := by
  have hpoint (u : ℝ) : 2 * (Real.sinh ((u + a) / 2) * Real.sinh ((u + b) / 2)) =
      Real.cosh (u + (a + b) / 2) - Real.cosh ((a - b) / 2) := by
    have h1 := Real.cosh_add ((u + a) / 2) ((u + b) / 2)
    have h2 := Real.cosh_sub ((u + a) / 2) ((u + b) / 2)
    rw [show (u + a) / 2 + (u + b) / 2 = u + (a + b) / 2 by ring] at h1
    rw [show (u + a) / 2 - (u + b) / 2 = (a - b) / 2 by ring] at h2
    linarith
  have he : 2 * sinePacketPair a b = ∫ u,
      Real.cosh (u + (a + b) / 2) * packet u ^ 2 -
        Real.cosh ((a - b) / 2) * packet u ^ 2 := by
    unfold sinePacketPair
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    linear_combination packet u ^ 2 * hpoint u
  have hc : Integrable (fun u => Real.cosh (u + (a + b) / 2) * packet u ^ 2) :=
    integrable_packet_weight ⟨fun u => Real.cosh (u + (a + b) / 2), by fun_prop⟩
  rw [integral_sub hc (integrable_packet_sq.const_mul _), packet_cosh_shift_integral,
    integral_const_mul, integral_sq_eq_autocorr_zero] at he
  change 2 * sinePacketPair a b = Real.cosh ((a + b) / 2) * packetCoshMass -
    Real.cosh ((a - b) / 2) * packetMass at he
  linarith

private theorem sinePacketPair_neg (a b : ℝ) : sinePacketPair (-a) (-b) = sinePacketPair a b := by
  rw [sinePacketPair_eq, sinePacketPair_eq,
    show (-a + -b) / 2 = -((a + b) / 2) by ring,
    show (-a - -b) / 2 = -((a - b) / 2) by ring, Real.cosh_neg, Real.cosh_neg]

private theorem sinePacketPair_comm (a b : ℝ) : sinePacketPair a b = sinePacketPair b a := by
  unfold sinePacketPair
  apply integral_congr_ae
  filter_upwards [] with u
  ring

private theorem weightedDiagonal_sine (a x : ℝ) :
    weightedDiagonal sineWeight a x = sinePacketPair a (a + x) := by
  unfold weightedDiagonal sineWeight sinePacketPair
  simp only [ContinuousMap.coe_mk, add_assoc]

/-- Exact multiplier leakage: the source zero survives while the sine correlation
is a positive growing hyperbolic factor times a fixed packet invariant. -/
theorem source_sinh_autocorr_lag (T : ℝ) :
    autocorr (sinhCompact (1 / 2) (source T)) lag =
      2 * Real.sinh (|T| + 2 * lag) * Real.sinh (lag / 2) * packetCoshMass := by
  have hf : (sinhCompact (1 / 2) (source T) : ℝ → ℝ) = fun u => sineWeight u * source T u := by
    funext u
    change Real.sinh ((1 / 2 : ℝ) * u) * source T u = Real.sinh (u / 2) * source T u
    rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  rw [hf, autocorr_weighted_source_lag]
  simp_rw [weightedDiagonal_sine]
  rw [show |T| + lag + lag = |T| + 2 * lag by ring,
    show |T| + 2 * lag + lag = |T| + 3 * lag by ring,
    show -(|T| + 2 * lag) + lag = -(|T| + lag) by ring,
    show -(|T| + 3 * lag) + lag = -(|T| + 2 * lag) by ring,
    sinePacketPair_neg, sinePacketPair_neg,
    sinePacketPair_comm (|T| + 2 * lag) (|T| + lag),
    sinePacketPair_comm (|T| + 3 * lag) (|T| + 2 * lag)]
  simp only [sinePacketPair_eq]
  rw [show (|T| + lag + (|T| + 2 * lag)) / 2 = (|T| + 2 * lag) - lag / 2 by ring,
    show (|T| + 2 * lag + (|T| + 3 * lag)) / 2 = (|T| + 2 * lag) + lag / 2 by ring,
    show (|T| + lag - (|T| + 2 * lag)) / 2 = -lag / 2 by ring,
    show (|T| + 2 * lag - (|T| + 3 * lag)) / 2 = -lag / 2 by ring,
    Real.cosh_sub]
  simp only [Real.cosh_add]
  ring

theorem source_sinh_autocorr_lag_pos (T : ℝ) :
    0 < autocorr (sinhCompact (1 / 2) (source T)) lag := by
  rw [source_sinh_autocorr_lag]
  have hd := lag_pos
  have h1 : 0 < Real.sinh (|T| + 2 * lag) := Real.sinh_pos_iff.mpr (by positivity)
  have h2 : 0 < Real.sinh (lag / 2) := Real.sinh_pos_iff.mpr (by positivity)
  exact mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) packetCoshMass_pos

/-- At fixed positive original energy and an exact source zero at `log 2`,
multiplier leakage exceeds any prescribed multiple of that original energy.
This concerns one logarithmic node, not the entire infinite source zero grid. -/
theorem exists_odd_logZero_large_sinhCorrelation (A : ℝ) :
    ∃ f : C_c(ℝ, ℝ), ContDiff ℝ ∞ (f : ℝ → ℝ) ∧ (∀ u, f (-u) = -f u) ∧
      autocorr f 0 = 6 * packetMass ∧ autocorr f (Real.log 2) = 0 ∧
        A * autocorr f 0 < autocorr (sinhCompact (1 / 2) f) (Real.log 2) := by
  let c := 2 * Real.sinh (lag / 2) * packetCoshMass
  have hc : 0 < c := mul_pos (mul_pos (by norm_num)
    (Real.sinh_pos_iff.mpr (by linarith [lag_pos]))) packetCoshMass_pos
  let T := (|A * (6 * packetMass)| + 1) / c
  have ht : 0 < T := div_pos (by positivity) hc
  have hct : c * T = |A * (6 * packetMass)| + 1 := by
    dsimp [T]
    field_simp [hc.ne']
  refine ⟨source T, sourceFn_smooth T, source_odd T, source_autocorr_zero T,
    source_autocorr_lag T, ?_⟩
  change A * autocorr (source T) 0 < autocorr (sinhCompact (1 / 2) (source T)) lag
  rw [source_autocorr_zero, source_sinh_autocorr_lag, abs_of_pos ht]
  have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ T + 2 * lag by linarith [lag_pos])
  have hm := mul_le_mul_of_nonneg_left hs hc.le
  change c * (T + 2 * lag) ≤ c * Real.sinh (T + 2 * lag) at hm
  have hval : 2 * Real.sinh (T + 2 * lag) * Real.sinh (lag / 2) * packetCoshMass =
      c * Real.sinh (T + 2 * lag) := by dsimp [c]; ring
  rw [hval]
  nlinarith [le_abs_self (A * (6 * packetMass)), lag_pos]

end
end GaloisForLFunctions.BiScaleUncertainty.OddMultiplierLeakage
