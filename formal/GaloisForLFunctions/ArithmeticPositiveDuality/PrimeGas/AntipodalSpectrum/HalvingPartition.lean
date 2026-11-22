import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ClockHalving

/-!
# Heat trace of the antipodal eigenspace at half time

The extra windings are the odd multiples of the old order. Their geometric
factor is nonvanishing throughout the open right half-plane. Each exceptional
clock thus gives the full scaled zeta divisor in a single eigenspace.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary

def halvingPartition (t : ExceptionalTime) : ℂ → ℂ := response (halfClock t)-response t

theorem halving_heat (t : ExceptionalTime) (s : ℂ) :
    HasSectorHeat (additional (halfClock t).val) s ↔ 1/2 < s.re := by
  rw [additional_heat_iff]
  exact ⟨fun h => h (additional_nonempty _ (by rw [twice_halfClock]; exact t.property)),fun h _ => h⟩

/-- The heat boundary of this one eigenspace detects norm preservation of the binary split. -/
theorem split_isometry_iff_halving_heat_boundary (t : ExceptionalTime) (s : ℂ) :
    (∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split s f x) ↔
      ¬HasSectorHeat (additional (halfClock t).val) s ∧
      ∀ δ : ℝ, 0 < δ → HasSectorHeat (additional (halfClock t).val) (s+(δ:ℂ)) := by
  rw [split_isometric_iff]
  simp only [halving_heat,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro he
    exact ⟨he.le,fun δ hδ => by linarith only [he,hδ]⟩
  · rintro ⟨hle,hr⟩
    apply le_antisymm hle
    by_contra! h
    have he := hr (1/2-s.re) (sub_pos.mpr h)
    linarith only [he]

theorem halving_trace (t : ExceptionalTime) (s : {z : ℂ // AbsoluteHeat (additional (halfClock t).val) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (additional (halfClock t).val) s) = halvingPartition t s.val := by
  have hβ := (halving_heat t _).mp ((sectorHeat_iff _ _).mpr s.property)
  have hs := additional_partition_sum (halfClock t).val ⟨s.val,hβ⟩
  change correction (2*(halfClock t).val) s.val + partition (additional (halfClock t).val) s.val =
    correction (halfClock t).val s.val at hs
  rw [twice_halfClock,response_eq_heat_sum t ⟨s.val,hβ⟩,response_eq_heat_sum (halfClock t) ⟨s.val,hβ⟩] at hs
  rw [operator_trace]
  change _ = response (halfClock t) s.val-response t s.val
  linear_combination hs

/-- The missing part of the unrestricted positive-winding sum consists of multiples of m. -/
theorem factor_deficit {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 1 < m) :
    2*q/(1-q)-factor m q = 2*q^m/(1-q^m) := by
  have hd : 1-q ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  have hn := one_sub_pow_ne hq hm.ne_zero
  have hqm : q*q^(m-1) = q^m := by rw [← pow_succ',Nat.sub_add_cancel hm.le]
  have hnum : 2*q*(1-q^(m-1)) = 2*(q-q^m) := by rw [← hqm]; ring
  rw [factor,hnum]
  field_simp [hd,hn]
  <;> ring

private theorem factor_step {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 1 < m) :
    factor (2*m) q-factor m q = 2*q^m/(1-q^(2*m)) := by
  have h₁ := factor_deficit hq hm
  have h₂ := factor_deficit hq (show 1 < 2*m by omega)
  have hn := one_sub_pow_ne hq hm.ne_zero
  have hpow : q^(2*m) = (q^m)^2 := by rw [Nat.mul_comm 2 m,pow_mul]
  have hsq := one_sub_pow_ne hq (show 2*m ≠ 0 by omega)
  rw [hpow] at h₂ hsq ⊢
  suffices h : 2*q^m/(1-q^m)-2*(q^m)^2/(1-(q^m)^2) = 2*q^m/(1-(q^m)^2) by
    linear_combination h₁-h₂+h
  field_simp [hn,hsq]
  <;> ring

theorem halving_formula (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) :
    halvingPartition t s.val = riemannZeta (2*s.val)*
      (2*(heat s.val (block t))^(windingOrder t)/(1-(heat s.val (block t))^(2*windingOrder t))) := by
  change riemannZeta _*factor _ _-riemannZeta _*factor _ _ = _
  rw [half_block,half_windingOrder,← mul_sub,factor_step (heat_contraction _ (block_nontrivial t) _ s.property) (order_nontrivial t)]

private theorem distinct_orders (t : ExceptionalTime) : windingOrder (halfClock t) ≠ windingOrder t := by
  rw [half_windingOrder]
  have := order_nontrivial t
  omega

theorem halving_meromorphic (t : ExceptionalTime) (s : ℂ) : MeromorphicAt (halvingPartition t) s :=
  (response_meromorphic _ s).sub (response_meromorphic _ s)

theorem halving_divisor (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) :
    meromorphicOrderAt (halvingPartition t) s.val = meromorphicOrderAt riemannZeta (2*s.val) :=
  same_block_difference_order (half_block t) (distinct_orders t) s

theorem halving_zero_iff (t : ExceptionalTime) (s : {z : ℂ // 0 < z.re}) :
    halvingPartition t s.val = 0 ↔ riemannZeta (2*s.val) = 0 :=
  sub_eq_zero.trans (same_block_coincidence (half_block t) (distinct_orders t) s)

theorem rh_iff_halving_zeros_isometric (t : ExceptionalTime) : RiemannHypothesis ↔
    ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2}, halvingPartition t s.val = 0 →
      ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_response_zeros_isometric t]
  apply forall_congr'
  intro s
  exact imp_congr ((response_zero_iff t ⟨_,s.property.1⟩).trans (halving_zero_iff t ⟨_,s.property.1⟩).symm) Iff.rfl

#print axioms halving_heat
#print axioms split_isometry_iff_halving_heat_boundary
#print axioms halving_trace
#print axioms factor_deficit
#print axioms halving_formula
#print axioms halving_meromorphic
#print axioms halving_divisor
#print axioms rh_iff_halving_zeros_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
