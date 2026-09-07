import GaloisForLFunctions.RHTower.ArithmeticStationaryQuadrantComparison
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.VanDerCorputWeightedSecondGeneral

/-!
# Exact reflected arithmetic cancellation of outgoing stationary tails

All literal outgoing tails factor through one common complex source integral.
Their sum therefore retains the reflected arithmetic partial sum before taking
norms. The complete stationary identity also keeps every finite pre-saddle head,
and at zeros retains the reflected pole, half endpoint, and remainder.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Integer frequency dilation at every positive real integration cutoff. -/
theorem integral_bernoulliFourierTerm_real_dilation (s : ℂ) {d : ℕ} (hd : 1 ≤ d)
    {a : ℝ} (ha : 0 < a) (k : ℤ) :
    (∫ x in Ioi a, bernoulliFourierTerm ((d:ℤ)*k) s x) =
      (d:ℂ)^(s-1) * ∫ x in Ioi ((d:ℝ)*a), bernoulliFourierTerm k s x := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hdR.ne'
  have he : (∫ x in Ioi a, bernoulliFourierTerm ((d:ℤ)*k) s x) =
      ∫ x in Ioi a, (d:ℂ)^s*bernoulliFourierTerm k s ((d:ℝ)*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact bernoulliFourierTerm_dilation s hd k (ha.trans hx)
  rw [he,integral_const_mul,integral_comp_mul_left_Ioi _ _ hdR,
    Complex.cpow_sub _ _ hdC,Complex.cpow_one]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,div_eq_mul_inv]
  ring

/-- The common actual first-frequency tail shared by all outgoing stationary modes. -/
def stationaryReflectedTailFactor (s : ℂ) (N : ℕ) : ℂ :=
  (N:ℂ)^(star s+1) * ∫ x in Ioi (s.im/(2*Real.pi)), bernoulliFourierTerm (-1) (star s) x

/-- The actual outgoing part of one normalized negative-frequency atom. -/
def stationaryOutgoingAtom (s : ℂ) (N k : ℕ) : ℂ :=
  (N:ℂ)^(star s+1) * ∫ x in Ioi (s.im/(2*Real.pi*k)), bernoulliFourierTerm (-(k:ℤ)) (star s) x

/-- The finite actual pre-saddle head of one normalized negative-frequency atom. -/
def stationaryIncomingAtom (s : ℂ) (N k : ℕ) : ℂ :=
  (N:ℂ)^(star s+1) * ∫ x in Ioc (N:ℝ) (s.im/(2*Real.pi*k)),
    bernoulliFourierTerm (-(k:ℤ)) (star s) x

/-- Frequency dependence of every outgoing tail is exactly a reflected Dirichlet coefficient. -/
theorem stationaryOutgoingAtom_eq_reflected_term {s : ℂ} (ht : 0 < s.im)
    (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    stationaryOutgoingAtom s N k = stationaryReflectedTailFactor s N*(k:ℂ)^(star s-1) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb : 0 < s.im/(2*Real.pi*k) := by positivity
  have h := integral_bernoulliFourierTerm_real_dilation (star s) hk hb (-1)
  have hc : (k:ℝ)*(s.im/(2*Real.pi*k)) = s.im/(2*Real.pi) := by field_simp
  simp only [Int.mul_neg,Int.mul_one,hc] at h
  rw [stationaryOutgoingAtom,h,stationaryReflectedTailFactor]
  ring

/-- A stationary atom splits into its literal finite head and outgoing integral. -/
theorem scaledBernoulliFourierAtom_eq_incoming_add_outgoing {s : ℂ} (hs : 0 < s.re)
    {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hstat : 2*Real.pi*k*N ≤ s.im) :
    scaledBernoulliFourierAtom s N (-(k:ℤ)) =
      stationaryIncomingAtom s N k+stationaryOutgoingAtom s N k := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hden : 0 < 2*Real.pi*(k:ℝ) := by positivity
  have hab : (N:ℝ) ≤ s.im/(2*Real.pi*k) := (le_div_iff₀ hden).mpr (by nlinarith)
  have hi := integrable_bernoulliFourierTerm hNp
    (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) (-(k:ℤ))
  unfold scaledBernoulliFourierAtom stationaryIncomingAtom stationaryOutgoingAtom
  rw [← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self)
    (hi.mono_set (show Ioi (s.im/(2*Real.pi*k)) ⊆ Ioi (N:ℝ) from fun x hx => hab.trans_lt hx))]
  ring

/-- Every finite outgoing family retains its entire reflected phase sum. -/
theorem sum_stationaryOutgoingAtom_eq_reflected_sum {s : ℂ} (ht : 0 < s.im)
    (N : ℕ) (F : Finset ℕ) (hF : ∀ k ∈ F, 1 ≤ k) :
    (∑ k ∈ F, stationaryOutgoingAtom s N k) =
      stationaryReflectedTailFactor s N * ∑ k ∈ F, (k:ℂ)^(star s-1) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k hk => stationaryOutgoingAtom_eq_reflected_term ht N (hF k hk))

/-- The magnitude identity keeps cancellation between frequencies before any estimate. -/
theorem norm_sum_stationaryOutgoingAtom_eq {s : ℂ} (ht : 0 < s.im)
    (N : ℕ) (F : Finset ℕ) (hF : ∀ k ∈ F, 1 ≤ k) :
    ‖∑ k ∈ F, stationaryOutgoingAtom s N k‖ =
      ‖stationaryReflectedTailFactor s N‖ * ‖∑ k ∈ F, (k:ℂ)^(star s-1)‖ := by
  rw [sum_stationaryOutgoingAtom_eq_reflected_sum ht N F hF,norm_mul]

/-- The ordinary reflected partial sum is the complete initial frequency coefficient sum. -/
theorem sum_reflected_frequency_eq_rawPrefix (s : ℂ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (k:ℂ)^(star s-1)) = rawPrefix (1-star s) K := by
  induction K with
  | zero => simp [rawPrefix]
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega),ih]
      simp only [rawPrefix,Finset.sum_range_succ,kernel]
      congr 2
      ring

/-- The full pre-saddle contribution is retained as a complex source sum. -/
def stationaryIncomingSection (s : ℂ) (N K : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, stationaryIncomingAtom s N k

/-- Exact whole-frequency decomposition, with all incoming heads and reflected cancellation retained. -/
theorem negativeFourierSection_eq_incoming_add_reflected {s : ℂ} (hs : 0 < s.re)
    (ht : 0 < s.im) {N K : ℕ} (hN : 1 ≤ N) (hK : 2*Real.pi*K*N ≤ s.im) :
    negativeFourierSection s N K = stationaryIncomingSection s N K+
      stationaryReflectedTailFactor s N*rawPrefix (1-star s) K := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : negativeFourierSection s N K = stationaryIncomingSection s N K+
      ∑ k ∈ Finset.Icc 1 K, stationaryOutgoingAtom s N k := by
    unfold negativeFourierSection stationaryIncomingSection
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk1,hkK⟩ := Finset.mem_Icc.mp hk
    have hkR : (k:ℝ) ≤ K := by exact_mod_cast hkK
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkR
      (show 0 ≤ 2*Real.pi by positivity)) hNr.le
    exact scaledBernoulliFourierAtom_eq_incoming_add_outgoing hs hN hk1 (hm.trans hK)
  rw [he,sum_stationaryOutgoingAtom_eq_reflected_sum ht N _ (fun k hk => (Finset.mem_Icc.mp hk).1),
    sum_reflected_frequency_eq_rawPrefix]

/-- The full stationary cutoff satisfies the actual frequency bound. -/
theorem stationary_cutoff_frequency_le {s : ℂ} (ht : 0 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    2*Real.pi*⌊s.im/(2*Real.pi*N)⌋₊*N ≤ s.im := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd : 0 < 2*Real.pi*(N:ℝ) := by positivity
  have hf := Nat.floor_le (div_nonneg ht hd.le)
  have h := (le_div_iff₀ hd).mp hf
  nlinarith

/-- Whole complex stationary budget, retaining reflected Dirichlet cancellation. -/
theorem stationaryComplexBudget_eq_incoming_add_reflected {s : ℂ} (hs : 0 < s.re)
    (ht : 0 < s.im) {N : ℕ} (hN : 1 ≤ N) :
    stationaryComplexBudget s N = stationaryIncomingSection s N ⌊s.im/(2*Real.pi*N)⌋₊+
      stationaryReflectedTailFactor s N*rawPrefix (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊ := by
  exact negativeFourierSection_eq_incoming_add_reflected hs ht hN (stationary_cutoff_frequency_le ht.le hN)

/-- The ordinary reflected partial sum retains its pole, half endpoint, and actual remainder. -/
theorem rawPrefix_reflected_eq (s : ℂ) (K : ℕ) :
    rawPrefix (1-star s) K = riemannZeta (1-star s)+(K:ℂ)^(star s)/(star s)+
      (K:ℂ)^(star s-1)/2+powerSumRemainder (1-star s) K := by
  unfold powerSumRemainder kernel
  rw [show 1-(1-star s)=star s by ring,show -(1-star s)=star s-1 by ring]
  ring

/-- At a strip zero only the reflected zeta value disappears from the partial sum. -/
theorem rawPrefix_reflected_eq_at_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : riemannZeta s=0) (K : ℕ) :
    rawPrefix (1-star s) K = (K:ℂ)^(star s)/(star s)+
      (K:ℂ)^(star s-1)/2+powerSumRemainder (1-star s) K := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  have hc : riemannZeta (star s)=0 := by rw [powerSum_zeta_star (by linarith) hs1,hz,star_zero]
  have hz' := (RHTower.riemannZeta_one_sub_eq_zero_iff
    (show 0 < (star s).re by simpa) (show (star s).re < 1 by simpa)).mpr hc
  rw [rawPrefix_reflected_eq,hz',zero_add]

/-- The actual logarithmic mode has a square-root cancellation bound on a doubling block,
uniformly in its linear frequency. -/
theorem norm_integral_logarithmicFourierMode_double_le {a β t : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (ht : 0 < t) (ω : ℝ) :
    ‖∫ x in a..(2*a), logarithmicFourierMode β t ω x‖ ≤ 20*a^(1-β)/Real.sqrt t := by
  have hab : a ≤ 2*a := by linarith
  have hx (x : ℝ) (hxx : x ∈ uIcc a (2*a)) : 0 < x :=
    ha.trans_le ((uIcc_of_le hab ▸ hxx).1)
  have hp (p : ℝ) : ContinuousOn (fun x : ℝ => x^p) (uIcc a (2*a)) := by
    intro x hxx
    exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hx x hxx).ne')).continuousAt.continuousWithinAt
  have hw (x : ℝ) (hxx : x ∈ uIcc a (2*a)) :
      HasDerivAt (fun x : ℝ => x^(-β)) (-β*x^(-β-1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (hx x hxx).ne')
  have hg (x : ℝ) (hxx : x ∈ uIcc a (2*a)) :
      HasDerivAt (fun x : ℝ => ω*x+t*Real.log x) (ω+t/x) x := by
    convert! ((hasDerivAt_id x).const_mul ω).add
      ((Real.hasDerivAt_log (hx x hxx).ne').const_mul t) using 1
    ring
  have hg' (x : ℝ) (hxx : x ∈ uIcc a (2*a)) :
      HasDerivAt (fun x : ℝ => ω+t/x) (-t/x^2) x := by
    convert! (((hasDerivAt_id x).inv (hx x hxx).ne').const_mul t).const_add ω using 1
    simp only [id_eq]
    ring
  have hg'' : ContinuousOn (fun x : ℝ => -t/x^2) (uIcc a (2*a)) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hxx => pow_ne_zero _ (hx x hxx).ne')
  have hb := RHTower.norm_integral_weight_cexp_secondDeriv_neg hab
    (by positivity : 0 < t/(2*a)^2) hw (continuousOn_const.mul (hp (-β-1)))
    (fun x hxx => Real.rpow_nonneg (hx x hxx).le _)
    (fun x hxx => mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (hx x hxx).le _))
    hg hg' hg'' (fun x hxx => by
      have hxu : x ≤ 2*a := (uIcc_of_le hab ▸ hxx).2
      have hsq : x^2 ≤ (2*a)^2 := by nlinarith [hx x hxx]
      have h := div_le_div_of_nonneg_left ht.le (sq_pos_of_pos (hx x hxx)) hsq
      simpa only [neg_div] using neg_le_neg h)
  change ‖∫ x in a..(2*a), logarithmicFourierMode β t ω x‖ ≤ _ at hb
  apply hb.trans_eq
  rw [Real.sqrt_div ht.le,Real.sqrt_sq (by positivity), ← endpoint_power_identity ha]
  field_simp
  ring

/-- Once the clock speed is at least half its limiting value, the complete tail has a reciprocal-frequency bound. -/
theorem norm_integral_logarithmicFourierMode_half_speed_le {a β t ω : ℝ}
    (ha : 0 < a) (hβ : 1 < β) (ht : 0 ≤ t) (hω : 0 < ω) (hcut : 2*t ≤ ω*a) :
    ‖∫ x in Ioi a, logarithmicFourierMode β (-t) ω x‖ ≤ 8*a^(-β)/ω := by
  have hfinite {b : ℝ} (hab : a ≤ b) :
      ‖∫ x in a..b, logarithmicFourierMode β (-t) ω x‖ ≤ 8*a^(-β)/ω := by
    have hx (x : ℝ) (hxx : x ∈ uIcc a b) : 0 < x := ha.trans_le ((uIcc_of_le hab ▸ hxx).1)
    have hp (p : ℝ) : ContinuousOn (fun x : ℝ => x^p) (uIcc a b) := by
      intro x hxx
      exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hx x hxx).ne')).continuousAt.continuousWithinAt
    have hw (x : ℝ) (hxx : x ∈ uIcc a b) :
        HasDerivAt (fun x : ℝ => x^(-β)) (-β*x^(-β-1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (hx x hxx).ne')
    have hg (x : ℝ) (hxx : x ∈ uIcc a b) :
        HasDerivAt (fun x : ℝ => ω*x+(-t)*Real.log x) (ω-t/x) x := by
      convert! ((hasDerivAt_id x).const_mul ω).add
        ((Real.hasDerivAt_log (hx x hxx).ne').const_mul (-t)) using 1
      ring
    have hg' (x : ℝ) (hxx : x ∈ uIcc a b) :
        HasDerivAt (fun x : ℝ => ω-t/x) (t/x^2) x := by
      convert! (hasDerivAt_const x ω).sub (((hasDerivAt_id x).inv (hx x hxx).ne').const_mul t) using 1
      simp only [id_eq]
      ring
    have hg'' : ContinuousOn (fun x : ℝ => t/x^2) (uIcc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) (fun x hxx => pow_ne_zero _ (hx x hxx).ne')
    have hb := RHTower.norm_integral_weight_cexp_le hab (by positivity : 0 < ω/2)
      hw (continuousOn_const.mul (hp (-β-1)))
      (fun x hxx => Real.rpow_nonneg (hx x hxx).le _)
      (fun x hxx => mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (hx x hxx).le _))
      hg hg' hg'' (fun x hxx => by
        have hax := (uIcc_of_le hab ▸ hxx).1
        have hdiv : t/x ≤ ω/2 := (div_le_iff₀ (hx x hxx)).mpr (by nlinarith)
        linarith) (fun x hxx => div_nonneg ht (sq_nonneg x))
    change ‖∫ x in a..b, logarithmicFourierMode β (-t) ω x‖ ≤ _ at hb
    convert! hb using 1
    ring
  have hlim := (intervalIntegral_tendsto_integral_Ioi a
    (integrable_logarithmicFourierMode ha hβ (-t) ω) tendsto_id).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop a] with b hb
  exact hfinite hb

/-- The whole outgoing saddle integral has a square-root height saving, with no asymptotic error term. -/
theorem norm_integral_logarithmicFourierMode_at_saddle_le {a β t ω : ℝ}
    (ha : 0 < a) (hβ : 1 < β) (ht : 1 ≤ t) (hω : 0 < ω) (hclock : ω*a=t) :
    ‖∫ x in Ioi a, logarithmicFourierMode β t (-ω) x‖ ≤ 28*a^(1-β)/Real.sqrt t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hab : a ≤ 2*a := by linarith
  have hi := integrable_logarithmicFourierMode ha hβ t (-ω)
  have hsplit : (∫ x in Ioi a, logarithmicFourierMode β t (-ω) x) =
      (∫ x in a..(2*a), logarithmicFourierMode β t (-ω) x)+
      ∫ x in Ioi (2*a), logarithmicFourierMode β t (-ω) x := by
    rw [intervalIntegral.integral_of_le hab, ← Ioc_union_Ioi_eq_Ioi hab,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hi.mono_set Ioc_subset_Ioi_self)
        (hi.mono_set (show Ioi (2*a) ⊆ Ioi a from fun x hx => hab.trans_lt hx))]
  have hnear := norm_integral_logarithmicFourierMode_double_le ha (by linarith : 0 < β) ht0 (-ω)
  have hfar0 := norm_integral_logarithmicFourierMode_half_speed_le
    (by positivity : 0 < 2*a) hβ ht0.le hω (by nlinarith : 2*t ≤ ω*(2*a))
  have hfar : ‖∫ x in Ioi (2*a), logarithmicFourierMode β t (-ω) x‖ ≤ 8*(2*a)^(-β)/ω := by
    have he (x : ℝ) : logarithmicFourierMode β t (-ω) x = star (logarithmicFourierMode β (-t) ω x) := by
      simpa only [neg_neg] using logarithmicFourierMode_neg β (-t) ω x
    simp_rw [he,Complex.star_def,integral_conj,Complex.norm_conj]
    exact hfar0
  have hp : (2*a)^(-β) ≤ a^(-β) := Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hsqrt : Real.sqrt t ≤ t := Real.sqrt_le_self_iff.mpr (Or.inr ht)
  have hfar' : 8*(2*a)^(-β)/ω ≤ 8*a^(1-β)/Real.sqrt t := by
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 8)) hω.le
    have he : 8*a^(-β)/ω = 8*a^(1-β)/t := by
      rw [← hclock,←endpoint_power_identity ha]
      field_simp
    rw [he] at hm
    exact hm.trans (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr ht0) hsqrt)
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hnear (hfar.trans hfar')).trans_eq (by ring))

/-- Explicit common-kernel ceiling with square-root height saving. -/
def stationaryReflectedTailEnvelope (s : ℂ) (N : ℕ) : ℝ :=
  28*(N:ℝ)^(s.re+1)*bernoulliModeWeight (-1)*(s.im/(2*Real.pi))^(-s.re-1)/Real.sqrt s.im

/-- The envelope is nonnegative in the positive-height chamber. -/
theorem stationaryReflectedTailEnvelope_nonneg {s : ℂ} (ht : 0 < s.im) (N : ℕ) :
    0 ≤ stationaryReflectedTailEnvelope s N := by
  have hb : 0 < s.im/(2*Real.pi) := by positivity
  unfold stationaryReflectedTailEnvelope
  exact div_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (bernoulliModeWeight_nonneg (-1))) (Real.rpow_nonneg hb.le _)) (Real.sqrt_nonneg _)

/-- The actual shared complex factor satisfies the explicit oscillatory ceiling. -/
theorem norm_stationaryReflectedTailFactor_le {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖stationaryReflectedTailFactor s N‖ ≤ stationaryReflectedTailEnvelope s N := by
  have ht0 : 0 < s.im := zero_lt_one.trans_le ht
  have hb : 0 < s.im/(2*Real.pi) := by positivity
  have he : (∫ x in Ioi (s.im/(2*Real.pi)), bernoulliFourierTerm (-1) (star s) x) =
      (bernoulliModeWeight (-1):ℂ) *
        ∫ x in Ioi (s.im/(2*Real.pi)), logarithmicFourierMode (s.re+2) s.im (-(2*Real.pi)) x := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [bernoulliFourierTerm,fourier_mul_cpow_eq_mode (-1) (star s) (hb.trans hx)]
    simp only [Complex.star_def,Complex.conj_re,Complex.conj_im,neg_neg,Int.cast_neg,
      Int.cast_one,mul_neg,mul_one]
  have hclock : (2*Real.pi)*(s.im/(2*Real.pi)) = s.im := by field_simp
  have h := norm_integral_logarithmicFourierMode_at_saddle_le hb
    (by linarith : 1 < s.re+2) ht (by positivity : 0 < 2*Real.pi) hclock
  rw [stationaryReflectedTailFactor,he,norm_mul,norm_mul,
    Complex.norm_natCast_cpow_of_pos (by omega : 0 < N),Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (bernoulliModeWeight_nonneg (-1))]
  simp only [Complex.add_re,Complex.star_def,Complex.conj_re,Complex.one_re]
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) (s.re+1)) (bernoulliModeWeight_nonneg (-1)))
  rw [← mul_assoc]
  apply hm.trans_eq
  unfold stationaryReflectedTailEnvelope
  rw [show 1-(s.re+2) = -s.re-1 by ring]
  ring

/-- Cancellation-sensitive bound for every finite outgoing frequency set. -/
theorem norm_sum_stationaryOutgoingAtom_le_reflected {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ s.im)
    {N : ℕ} (hN : 1 ≤ N) (F : Finset ℕ) (hF : ∀ k ∈ F, 1 ≤ k) :
    ‖∑ k ∈ F, stationaryOutgoingAtom s N k‖ ≤
      stationaryReflectedTailEnvelope s N * ‖∑ k ∈ F, (k:ℂ)^(star s-1)‖ := by
  rw [norm_sum_stationaryOutgoingAtom_eq (zero_lt_one.trans_le ht) N F hF]
  exact mul_le_mul_of_nonneg_right (norm_stationaryReflectedTailFactor_le hs ht hN) (norm_nonneg _)

/-- The entire difference from the incoming section retains the reflected arithmetic cancellation. -/
theorem norm_negativeFourierSection_sub_incoming_le {s : ℂ} (hs : 0 < s.re) (ht : 1 ≤ s.im)
    {N K : ℕ} (hN : 1 ≤ N) (hK : 2*Real.pi*K*N ≤ s.im) :
    ‖negativeFourierSection s N K-stationaryIncomingSection s N K‖ ≤
      stationaryReflectedTailEnvelope s N*‖rawPrefix (1-star s) K‖ := by
  rw [negativeFourierSection_eq_incoming_add_reflected hs (zero_lt_one.trans_le ht) hN hK,
    add_sub_cancel_left,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_stationaryReflectedTailFactor_le hs ht hN) (norm_nonneg _)

/-- Full-source inequality with only the pre-saddle head left outside the reflected cancellation bound. -/
theorem normalizedWeightedRemainder_scaled_im_le_incoming_reflected {s : ℂ}
    (hs : 0 < s.re) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ)^(2*s.re+1)*(normalizedWeightedRemainder s N).im ≤
      (stationaryIncomingSection s N ⌊s.im/(2*Real.pi*N)⌋₊).im+
      stationaryReflectedTailEnvelope s N*‖rawPrefix (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊‖+
      1/(12*(2*Real.pi*N+s.im))-s.im/(12*Complex.normSq (s+1)) := by
  have ht0 : 0 < s.im := zero_lt_one.trans_le ht
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have h := normalizedWeightedRemainder_scaled_im_le_stationary_budget hs hs1 ht0.le hN
  rw [←stationaryComplexBudget_im ht0.le hN,
    stationaryComplexBudget_eq_incoming_add_reflected hs ht0 hN,Complex.add_im] at h
  have hc := mul_le_mul_of_nonneg_right (norm_stationaryReflectedTailFactor_le hs ht hN)
    (norm_nonneg (rawPrefix (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊))
  rw [←norm_mul] at hc
  have him := (Complex.im_le_norm _).trans hc
  linarith

/-- Explicit scalar ceiling for the reflected partial sum at a strip zero. -/
def reflectedPrefixZeroEnvelope (s : ℂ) (K : ℕ) : ℝ :=
  (K:ℝ)^s.re/‖s‖+(K:ℝ)^(s.re-1)/2+
    (‖(1-star s)*(2-star s)‖/(2-s.re))*(K:ℝ)^(s.re-2)

/-- Reflected zero cancellation leaves only the known endpoint terms and a bounded actual remainder. -/
theorem norm_rawPrefix_reflected_le_at_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : riemannZeta s=0) {K : ℕ} (hK : 1 ≤ K) :
    ‖rawPrefix (1-star s) K‖ ≤ reflectedPrefixZeroEnvelope s K := by
  have hK0 : 0 < K := by omega
  have hr0 : -1 < (1-star s).re := by simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; linarith
  have hr1 : (1:ℂ)-star s ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re] at he
    linarith
  have hr := norm_powerSumRemainder_le hr0 hr1 hK
  simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re] at hr
  have hnormA : ‖(K:ℂ)^(star s)/(star s)‖ = (K:ℝ)^s.re/‖s‖ := by
    rw [norm_div,Complex.norm_natCast_cpow_of_pos hK0]
    simp only [Complex.star_def,Complex.conj_re,Complex.norm_conj]
  have hnormB : ‖(K:ℂ)^(star s-1)/2‖ = (K:ℝ)^(s.re-1)/2 := by
    rw [norm_div,Complex.norm_natCast_cpow_of_pos hK0]
    simp only [Complex.sub_re,Complex.star_def,Complex.conj_re,Complex.one_re,Complex.norm_ofNat]
  rw [rawPrefix_reflected_eq_at_zero hs hs' hz]
  calc
    _ ≤ ‖(K:ℂ)^(star s)/(star s)+(K:ℂ)^(star s-1)/2‖+‖powerSumRemainder (1-star s) K‖ := norm_add_le _ _
    _ ≤ (‖(K:ℂ)^(star s)/(star s)‖+‖(K:ℂ)^(star s-1)/2‖)+
        (‖(1-star s)*((1-star s)+1)‖/((1-s.re)+1))*(K:ℝ)^(-(1-s.re)-1) :=
      add_le_add (norm_add_le _ _) hr
    _ = _ := by
      rw [hnormA,hnormB]
      unfold reflectedPrefixZeroEnvelope
      rw [show (1:ℂ)-star s+1=2-star s by ring,show (1-s.re)+1=2-s.re by ring,
        show -(1-s.re)-1=s.re-2 by ring]

/-- At a zero the entire outgoing sector has an explicit parameter-only bound. -/
theorem norm_negativeFourierSection_sub_incoming_le_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s=0)
    {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) (hstat : 2*Real.pi*K*N ≤ s.im) :
    ‖negativeFourierSection s N K-stationaryIncomingSection s N K‖ ≤
      stationaryReflectedTailEnvelope s N*reflectedPrefixZeroEnvelope s K := by
  exact (norm_negativeFourierSection_sub_incoming_le hs ht hN hstat).trans
    (mul_le_mul_of_nonneg_left (norm_rawPrefix_reflected_le_at_zero hs hs' hz hK)
      (stationaryReflectedTailEnvelope_nonneg (zero_lt_one.trans_le ht) N))

/-- The exact whole-sector identity at zeros retains both reflected boundary terms and the remainder. -/
theorem stationaryComplexBudget_eq_incoming_reflected_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (ht : 0 < s.im) (hz : riemannZeta s=0)
    {N : ℕ} (hN : 1 ≤ N) :
    stationaryComplexBudget s N = stationaryIncomingSection s N ⌊s.im/(2*Real.pi*N)⌋₊+
      stationaryReflectedTailFactor s N *
        ((⌊s.im/(2*Real.pi*N)⌋₊:ℂ)^(star s)/(star s)+
         (⌊s.im/(2*Real.pi*N)⌋₊:ℂ)^(star s-1)/2+
         powerSumRemainder (1-star s) ⌊s.im/(2*Real.pi*N)⌋₊) := by
  rw [stationaryComplexBudget_eq_incoming_add_reflected hs ht hN,rawPrefix_reflected_eq_at_zero hs hs' hz]

/-- A closed-right zero has a nonempty actual stationary unit sector. -/
theorem stationary_unit_cutoff_pos_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s=0) :
    1 ≤ ⌊s.im/(2*Real.pi)⌋₊ := by
  by_contra hn
  have hK : ⌊s.im/(2*Real.pi)⌋₊=0 := by omega
  have he : stationaryComplexBudget s 1=0 := by
    simp [stationaryComplexBudget,negativeFourierSection,hK]
  have hi := stationaryComplexBudget_im (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))
  rw [he,Complex.zero_im] at hi
  have hp := stationaryFourierBudget_pos_at_closed_right_zero hs hs' ht hz
  linarith

/-- The zero-forced stationary lower budget transfers to the actual incoming head,
with an explicit bound for the entire outgoing sector. -/
theorem stationaryIncomingSection_im_lowerBound_at_closed_right_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 1 ≤ s.im) (hz : riemannZeta s=0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      s.im/(12*Complex.normSq (s+1))-1/(12*(2*Real.pi+s.im))-
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ ≤
        (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  have hs0 : 0 < s.re := by linarith
  have hstat := stationary_cutoff_frequency_le (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))
  simp only [Nat.cast_one,mul_one] at hstat
  have hb := norm_negativeFourierSection_sub_incoming_le_at_zero hs0 hs' ht hz
    (by rfl : 1 ≤ (1:ℕ)) (stationary_unit_cutoff_pos_at_closed_right_zero hs hs' ht hz)
    (by simpa only [Nat.cast_one,mul_one] using hstat)
  have hc : ‖stationaryComplexBudget s 1-stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊‖ ≤
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ := by
    simpa only [stationaryComplexBudget,Nat.cast_one,mul_one] using hb
  have him := Complex.im_le_norm (stationaryComplexBudget s 1-
    stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊)
  rw [Complex.sub_im,stationaryComplexBudget_im (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))] at him
  have hl := stationaryFourierBudget_lowerBound_at_zero hs0 hs' (by linarith) hz
  linarith

end RHTower.DeletionMixedRefinement
