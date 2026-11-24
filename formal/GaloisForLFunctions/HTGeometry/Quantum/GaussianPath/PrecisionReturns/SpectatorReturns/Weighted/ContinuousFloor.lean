import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.WindingFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.GapClock

/-! # Continuous spectral returns with unequal phase tolerances -/

open Finset Filter Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

/-- Read the tightest phase as the winding clock. Its rounding error
enlarges every remaining phase tolerance by at most a fixed ratio factor. -/
theorem winding_of_box {n : ℕ} (g : Fin (n+1)→ℝ) (hg : g 0≠0) (r : Fin (n+1)→ℝ)
    (hmin : ∀ i : Fin n, r 0≤r i.succ) {a t : ℝ} (ha : 0<a) (hat : a≤t)
    (hr : r 0<a*|g 0|/(2*π)) (h : ∀ i, latticeClose (gapTurn g t i) (r i)) :
    ∃ q : ℕ, 0<q ∧ (q:ℝ)≤2*(|g 0|/(2*π))*t ∧ ∃ p : Fin n→ℤ,
      ∀ i, |(q:ℝ)*gapRatio g i.succ-(p i:ℝ)|≤(1+‖gapRatio g‖)*r i.succ := by
  choose k hk using h
  let q := k 0
  have hbig : r 0<t*|g 0|/(2*π) := hr.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hat (abs_nonneg _)) two_pi_pos.le)
  have hq : q≠0 := by
    intro hz
    have h₀ := hk 0
    change |gapTurn g t 0-(q:ℝ)|<r 0 at h₀
    rw [hz,Int.cast_zero,sub_zero,gapTurn,abs_div,abs_mul,abs_of_pos (ha.trans_le hat),abs_of_pos two_pi_pos] at h₀
    exact hbig.asymm h₀
  have hn : (q.natAbs:ℝ)=|(q:ℝ)| := by rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  refine ⟨q.natAbs,Int.natAbs_pos.mpr hq,?_,?_⟩
  · have h₁ := abs_winding_le_of_continuousReturn g (hk 0)
    rw [abs_of_pos (ha.trans_le hat)] at h₁
    rw [hn]; change |(k 0:ℝ)|≤_
    exact h₁.trans ((add_le_add le_rfl hbig.le).trans_eq (by ring))
  have hh (i : Fin n) : |(q:ℝ)*gapRatio g i.succ-(k i.succ:ℝ)|≤(1+‖gapRatio g‖)*r i.succ := by
    let y := gapRatio g i.succ
    have h₀ := hk 0
    have h₁ := hk i.succ
    have he : (q:ℝ)*y-(k i.succ:ℝ)=((q:ℝ)-gapTurn g t 0)*y+(gapTurn g t i.succ-(k i.succ:ℝ)) := by
      have hturn := gapTurn_zero_mul_gapRatio g hg t i.succ
      dsimp only [y]; linarith only [hturn]
    have hr₀ := (abs_nonneg _).trans h₀.le
    have hs : |(q:ℝ)-gapTurn g t 0|≤r i.succ := by rw [abs_sub_comm]; exact h₀.le.trans (hmin i)
    have hy : |y|≤‖gapRatio g‖ := norm_le_pi_norm (gapRatio g) i.succ
    rw [he]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul]
    linarith only [mul_le_mul hs hy (abs_nonneg _) (hr₀.trans (hmin i)),h₁]
  rcases le_or_gt (0:ℝ) q with hp|hn'
  · refine ⟨fun i => k i.succ,fun i => ?_⟩
    rw [hn,abs_of_nonneg hp]
    exact hh i
  refine ⟨fun i => -k i.succ,fun i => ?_⟩
  rw [hn,abs_of_neg hn',neg_mul,Int.cast_neg,neg_sub_neg,abs_sub_comm]
  exact hh i

/-- For independent strongly extremal ratios, the lower physical-time
exponent is the sum of the weights other than the tightest clock. -/
theorem weighted_gap_floor {n : ℕ} (hn : 0<n) (g : Fin (n+1)→ℝ) (hg : g 0≠0)
    (hy : ¬KleinbockMargulis.VWMA (fun i : Fin n => gapRatio g i.succ))
    (w : Fin (n+1)→ℝ) (hw : ∀ i, 0<w i) (hmax : ∀ i : Fin n, w i.succ≤w 0)
    {a K lo : ℝ} (ha : 0<a) (hK : 0<K) (hlo : 0≤lo) (hs : lo<∑ i : Fin n, w i.succ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t≥a, (∀ i, latticeClose (gapTurn g t i) (K*ε^(w i))) →
      lo<log t/log (1/ε) := by
  let S := ∑ i : Fin n, w i.succ
  let u := fun i : Fin n => w i.succ/S
  let L := (lo+S)/2
  let B := 2*(|g 0|/(2*π))
  have hS : 0<S := hlo.trans_lt hs
  have hL : lo<L := by dsimp only [L]; linarith only [hs]
  have hL' : L<S := by dsimp only [L]; linarith only [hs]
  have hB : 0<B := by dsimp only [B]; positivity
  have hu i : 0<u i := div_pos (hw _) hS
  have hsum : ∑ i, u i=1 := by simp only [u,←sum_div,S,div_self hS.ne']
  have heq i : S*u i=w i.succ := by dsimp only [u]; field_simp [hS.ne']
  have hK' : 0<(1+‖gapRatio g‖)*K := mul_pos (by positivity) hK
  have hfloor := weighted_winding_floor hn hy u hu hsum (hL:=hlo.trans hL.le) hL' hK'
  have hr : Tendsto (fun ε : ℝ => K*ε^(w 0)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => K*ε^(w 0)) 0 :=
      continuousAt_const.mul (continuousAt_rpow_const 0 (w 0) (Or.inr (hw 0).le))
    simpa only [zero_rpow (hw 0).ne',mul_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hcorr := (tendsto_const_div_log_one_div (log B)).eventually_lt_const (sub_pos.mpr hL)
  have hcut : 0<a*|g 0|/(2*π) := div_pos (mul_pos ha (abs_pos.mpr hg)) two_pi_pos
  filter_upwards [hfloor,hr.eventually_lt_const hcut,hcorr,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hh hε hc he
  intro t hat ht
  obtain ⟨q,hq,hqt,p,hp⟩ := winding_of_box g hg (fun i => K*ε^(w i))
    (fun i => mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_ge he.1 he.2.le (hmax i)) hK.le) ha hat hε ht
  have hl := hh q hq p (fun i => by simpa only [heq,mul_assoc] using hp i)
  have hlog := log_lt_log (rpow_pos_of_pos he.1 _) (hl.trans_le hqt)
  change log (ε^(-L))<log (B*t) at hlog
  rw [log_rpow he.1,log_mul hB.ne' (ha.trans_le hat).ne'] at hlog
  have hden := log_pos ((one_lt_div he.1).mpr he.2)
  rw [lt_div_iff₀ hden,one_div,log_inv]
  rw [div_lt_iff₀ hden,one_div,log_inv] at hc
  linarith only [hc,hlog]

#print axioms weighted_gap_floor
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
