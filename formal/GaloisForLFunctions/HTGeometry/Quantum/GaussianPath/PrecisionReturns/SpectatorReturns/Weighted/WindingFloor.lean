import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.Sides

/-! # Lower clock exponent for simultaneous returns at different precisions -/

open Finset Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
open KleinbockMargulis
noncomputable section

/-- Errors of orders ε^(S uᵢ), for positive weights of sum one, require
a denominator above ε^(-L) for every L<S. The bound includes all windings
and all integer approximants at each sufficiently small tolerance. -/
theorem weighted_winding_floor {n : ℕ} (hn : 0<n) {y : Fin n→ℝ} (hy : ¬VWMA y)
    (u : Fin n→ℝ) (hu : ∀ i, 0<u i) (hsum : ∑ i, u i=1)
    {S L K : ℝ} (hL : 0≤L) (hS : L<S) (hK : 0<K) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ q : ℕ, 0<q → ∀ p : Fin n→ℤ,
      (∀ i, |(q:ℝ)*y i-(p i:ℝ)|≤K*ε^(S*u i)) → ε^(-L)<(q:ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨j,_,hj⟩ := exists_min_image univ u univ_nonempty
  let d := (S-L)*(u j)/(2*(L+1))
  have hd : 0<d := div_pos (mul_pos (sub_pos.mpr hS) (hu j)) (by positivity)
  let η := (S-L)*(u j)-L*d
  have hη : 0<η := by
    have he : (S-L)*u j=d*(2*(L+1)) := (div_mul_cancel₀ _ (by positivity : 2*(L+1)≠0)).symm
    dsimp only [η]
    rw [he]; nlinarith only [hd,mul_nonneg hL hd.le]
  obtain ⟨C,hC,hbox⟩ := weighted_error_bound hn hy hd
  have hsmall : Tendsto (fun ε : ℝ => C*((n:ℝ)*(K*ε^η))) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => C*((n:ℝ)*(K*ε^η))) 0 :=
      continuousAt_const.mul (continuousAt_const.mul (continuousAt_const.mul
        (continuousAt_rpow_const 0 η (Or.inr hη.le))))
    simpa only [zero_rpow hη.ne',mul_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  filter_upwards [hsmall.eventually_lt_const zero_lt_one,Ioo_mem_nhdsGT (zero_lt_one' ℝ)]
    with ε hsmall hε
  intro q hq p hp
  by_contra! hshort
  have hq' : 0<(q:ℝ) := Nat.cast_pos.mpr hq
  have hqpow : (q:ℝ)^d*(q:ℝ)^(-d)=1 := by rw [←rpow_add hq',add_neg_cancel,rpow_zero]
  have hh := mul_le_mul_of_nonneg_left (hbox q hq p u (fun i => (hu i).le) hsum) (rpow_nonneg hq'.le d)
  rw [hqpow,mul_left_comm ((q:ℝ)^d) C,mul_sum] at hh
  have each (i : Fin n) : (q:ℝ)^d*((q:ℝ)^(u i)*|(q:ℝ)*y i-(p i:ℝ)|)≤K*ε^η := by
    rw [←mul_assoc,←rpow_add hq']
    have hpower := rpow_le_rpow hq'.le hshort (add_nonneg hd.le (hu i).le)
    have hm := mul_le_mul hpower (hp i) (abs_nonneg _) (rpow_nonneg (rpow_nonneg hε.1.le _) _)
    refine hm.trans ?_
    rw [←rpow_mul hε.1.le,mul_left_comm _ K,←rpow_add hε.1]
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply rpow_le_rpow_of_exponent_ge hε.1 hε.2.le
    have hmin := mul_le_mul_of_nonneg_left (hj i (mem_univ i)) (sub_nonneg.mpr hS.le)
    dsimp only [η]; linarith only [hmin]
  have htotal := mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _ => each i)) (zero_le_one.trans hC)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at htotal
  exact hsmall.not_ge (hh.trans htotal)

#print axioms weighted_winding_floor
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
