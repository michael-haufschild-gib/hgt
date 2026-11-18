import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.PoleMomentsFromSeparatedGraphContacts
import GaloisForLFunctions.CountingHolography.Sections.SignedSplineSmallSections
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds

/-!
# Finite graph orders for the pole correction

On each prescribed signed integer spline ray, the separated vertical graph orders
can replace both sampled pole degrees in the signed section limit. The fixed
finite-place ideal and the regularized jet pairing are those of the original ray.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography
open ArithmeticCastelnuovoSeveri _root_.RHTower
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry Finset Polynomial

private theorem ray_moment_limit {N : ℕ} (a : Fin N → ℤ) (t : ℝ) :
    Tendsto (fun m : ℕ => sampledDegree (packet (m • a)) (3*windowEnd N) (resolution (m • a)) t / m)
      atTop (𝓝 (ccmRealExponentialMoment t (packet a))) := by
  by_cases ha : a = 0
  · subst a
    simp [packet,splineSource,ccmRealExponentialMoment,ccmRealExponentialTilt,sampledDegree,degreeSample]
  have h := (tendsto_sampledDegree (packet_contDiff a).continuous (packet_window a).1
    (packet_window a).2 t).comp (tendsto_resolution_ray ha)
  apply h.congr' ((eventually_ge_atTop 1).mono fun m hm => ?_)
  change sampledDegree (packet a) _ _ t = _
  rw [packet_smul,sampledDegree_mul,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt hm)]

/-- Quotient of the two effective vertical orders. The square accounts for the
two orientations in the directed graph height. -/
private def orderQuotient (A X B : ℕ) (u v : ℕ → ℤ) : ℚ :=
  ((signedDivisorOrder A X B u v : ℚ) / signedDivisorOrder A X B u (-v))^2

private theorem order_pos {A : ℕ} (hA : 0 < A) (X B : ℕ) (u v : ℕ → ℤ) :
    0 < signedDivisorOrder A X B u v := by
  apply Finset.prod_pos
  intro i hi
  have hi' := hA.trans_le (Finset.mem_Icc.mp hi).1
  rw [divisorRowOrder,verticalIntersection_eq,Finset.prod_singleton]
  apply Finset.prod_pos
  intro j hj
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hn,ht'⟩ := Finset.mem_erase.mp ht
  have h1 := (Finset.mem_Icc.mp ht').1
  have hlt : 1 < t := by omega
  apply pow_pos
  apply Nat.pos_of_ne_zero
  apply Int.natAbs_ne_zero.mpr
  apply mt content_eq_zero_iff.mp
  apply sub_ne_zero.mpr
  exact conductorContact_graph_ne hi'.ne' (Nat.mul_ne_zero hi'.ne' (by omega))
    (lt_mul_of_one_lt_right hi' hlt).ne

private theorem orderQuotient_spec {A : ℕ} (hA : 0 < A) (X B : ℕ) (u v : ℕ → ℤ) :
    0 < orderQuotient A X B u v ∧
      Real.log (orderQuotient A X B u v : ℝ) = 2*signedDivisorHeight A X B u v := by
  have hp := order_pos hA X B u v
  have hn := order_pos hA X B u (-v)
  unfold orderQuotient signedDivisorHeight
  refine ⟨pow_pos (div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr hn)) _,?_⟩
  simp only [Rat.cast_pow,Rat.cast_div,Rat.cast_natCast,Real.log_pow,Nat.cast_ofNat,
    Real.log_div (Nat.cast_ne_zero.mpr hp.ne') (Nat.cast_ne_zero.mpr hn.ne')]

/-- Finite-place multiplier obtained from the two sampled integral graph divisors. -/
def sampledOrderQuotient (s B : ℕ) (R : ℝ) (f g : ℝ → ℝ) : ℚ :=
  let N := s.sqrt
  orderQuotient N (N*B) B
    (fun i => ⌊(s:ℝ)*(Real.sqrt i * logCellWidth i * logSamples f R N i)⌋)
    (fun j => ⌊(s:ℝ)*(logSamples g R N j / Real.sqrt j)⌋)

theorem sampledOrderQuotient_spec {s : ℕ} (hs : 0 < s) (B : ℕ) (R : ℝ) (f g : ℝ → ℝ) :
    0 < sampledOrderQuotient s B R f g ∧
      Real.log (sampledOrderQuotient s B R f g : ℝ) = sampledGraphHeight s B R f g :=
  orderQuotient_spec (Nat.sqrt_pos.mpr hs) _ _ _ _

/-- The actual rational quotient of restriction orders at separation r⁴. -/
def separatedPoleQuotient {N : ℕ} (a : Fin N → ℤ) (R : ℝ) (B r s : ℕ) : ℚ :=
  sampledOrderQuotient s (B*(r^4+1)) R (packet a)
    (fun v => packet a (v-Real.log ((r^4 : ℕ) : ℝ)))

private theorem effective_orderQuotient {A : ℕ} (hA : 0 < A) (X B : ℕ) (u v : ℕ → ℤ)
    (hu : ∀ i, 0 < i → 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) :
    ∃ c : ℕ, 0 < c ∧ orderQuotient A X B u v = (c : ℚ)^2 := by
  have hone : signedDivisorOrder A X B u (-v) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hui := hu i (hA.trans_le (Finset.mem_Icc.mp hi).1)
    have hsign : 0 ≤ (u i).sign := by
      rcases hui.eq_or_lt with he | ht
      · simp [← he]
      · simp only [Int.sign_eq_one_of_pos ht,zero_le_one]
    rw [divisorRowOrder,verticalIntersection_eq,Finset.prod_singleton]
    refine Finset.prod_eq_one fun j _ => ?_
    have hz : ((u i).sign * (-v) j).toNat = 0 :=
      Int.toNat_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos hsign (neg_nonpos.mpr (hv j)))
    rw [hz,Nat.mul_zero,pow_zero]
  refine ⟨_,order_pos hA X B u v,?_⟩
  simp only [orderQuotient,hone,Nat.cast_one,div_one]

/-- For an effective integer ray the entire pole multiplier is the square of
one positive integral restriction order. -/
theorem separatedPoleQuotient_effective {N : ℕ} (a : Fin N → ℕ) (R : ℝ) (B r : ℕ)
    {s : ℕ} (hs : 0 < s) : ∃ c : ℕ, 0 < c ∧
      separatedPoleQuotient (fun i => (a i : ℤ)) R B r s = (c : ℚ)^2 := by
  have hf (v : ℝ) : 0 ≤ packet (fun i => (a i : ℤ)) v := by
    unfold packet splineSource
    apply Finset.sum_nonneg
    intro i _
    have hcoef : (0 : ℝ) ≤ ((a i : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      exact Nat.cast_nonneg _
    exact mul_nonneg hcoef (BiScaleUncertainty.ChebyshevGauge.cubicSpline_nonneg _)
  unfold separatedPoleQuotient sampledOrderQuotient
  apply effective_orderQuotient (Nat.sqrt_pos.mpr hs)
  · intro i hi
    exact Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (logCellWidth_pos hi).le) (hf _)))
  · intro j
    exact Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hf _) (Real.sqrt_nonneg _)))

/-- Thicken the moving restriction by an integral factor so its order supplies
the pole contribution at the original multiplicity m. -/
def poleAdjustedGenerator {N : ℕ} (a : Fin N → ℤ) (R : ℝ) (B m r s : ℕ) : ℚ :=
  generator (m • a) / (separatedPoleQuotient a R B r s)^(m^2/(r*s)^2)

theorem poleAdjustedGenerator_pos {N : ℕ} (a : Fin N → ℤ) (R : ℝ) (B m r : ℕ) {s : ℕ} (hs : 0 < s) :
    0 < poleAdjustedGenerator a R B m r s :=
  div_pos (contactGenerator_pos _ _ _) (pow_pos (sampledOrderQuotient_spec hs _ _ _ _).1 _)

private theorem fourth_power_normalization (v : ℝ) (n s : ℕ) :
    v/(s:ℝ)^2/Real.sqrt ((n^4 : ℕ) : ℝ) = v/((n*s : ℕ) : ℝ)^2 := by
  rw [Nat.cast_pow,show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _),
    div_div,Nat.cast_mul,mul_pow,mul_comm ((s:ℝ)^2)]

/-- Let the auxiliary scale grow slowly enough that a whole number of graph
orders fills the original quadratic scale with relative rounding error ≤ 1/m. -/
private theorem integral_repetitions (d : ℕ → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun m : ℕ => ((m^2/(d (j m))^2 : ℕ) : ℝ)*(d (j m) : ℝ)^2/(m:ℝ)^2)
        atTop (𝓝 1) := by
  let j (m : ℕ) := Nat.findGreatest (fun i => (d i)^2 ≤ m) m
  have hj : Tendsto j atTop atTop := by
    rw [tendsto_atTop]
    intro k
    filter_upwards [eventually_ge_atTop k,eventually_ge_atTop ((d k)^2)] with m hkm hdm
    exact Nat.le_findGreatest (P := fun i => (d i)^2 ≤ m) hkm hdm
  have hcut : ∀ᶠ m in atTop, (d (j m))^2 ≤ m :=
    (eventually_ge_atTop ((d 0)^2)).mono fun m hm =>
      Nat.findGreatest_spec (P := fun i => (d i)^2 ≤ m) (Nat.zero_le m) hm
  let rem (m : ℕ) := m^2 % (d (j m))^2
  have hz : Tendsto (fun m : ℕ => (rem m : ℝ)/(m:ℝ)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (g := fun m : ℕ => 1/(m : ℝ))
    · filter_upwards [hcut,eventually_ge_atTop 1] with m hm hm1
      have hr := (Nat.mod_lt (m^2) (pow_pos (hd (j m)) 2)).le.trans hm
      calc (rem m : ℝ)/(m:ℝ)^2 ≤ (m:ℝ)/(m:ℝ)^2 :=
             div_le_div_of_nonneg_right (by exact_mod_cast hr) (sq_nonneg _)
           _ = _ := by field_simp [(Nat.cast_pos.mpr hm1 : 0 < (m:ℝ)).ne']
    · exact tendsto_one_div_atTop_nhds_zero_nat
  refine ⟨j,hj,?_⟩
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  rw [sub_zero] at h
  apply h.congr' ((eventually_ge_atTop 1).mono fun m hm => ?_)
  have he : (rem m : ℝ) + (d (j m):ℝ)^2 * ((m^2/(d (j m))^2 : ℕ):ℝ) = (m:ℝ)^2 := by
    exact_mod_cast Nat.mod_add_div (m^2) ((d (j m))^2)
  change 1 - (rem m:ℝ)/(m:ℝ)^2 = _
  field_simp [(Nat.cast_pos.mpr hm : 0 < (m:ℝ)).ne']
  linarith only [he]

/-- At every original multiplicity m the corrected finite-place ideal has integral
valuations. Its signed degree using just the original real jets recovers the full
Weil form on every prescribed integer ray. -/
theorem integerProbe_from_separated_orders_and_jets {N : ℕ} (a : Fin N → ℤ) :
    ∃ (R : ℝ) (B : ℕ) (r s : ℕ → ℕ), 0 < R ∧ 1 ≤ B ∧ (∀ m, 0 < s m) ∧
      Tendsto r atTop atTop ∧ Tendsto s atTop atTop ∧ Tendsto (fun m : ℕ =>
        (-degreeForm (packet (m • a)) (3*windowEnd N) (resolution (m • a)) -
          Real.log (poleAdjustedGenerator a R B m (r m) (s m) : ℝ))/(m : ℝ)^2)
        atTop (𝓝 (integerProbe N a)) := by
  obtain ⟨R,B,M,hw,hlim⟩ := separated_graph_orders_recover_pole (packet_contDiff a) (packet_contDiff a)
    (packet_hasCompactSupport a) (packet_hasCompactSupport a)
  let k (n : ℕ) := max (n+1) (M n)
  let s₀ (n : ℕ) := k (n^4)
  let d (i : ℕ) := (i+1)*s₀ (i+1)
  have hs₀ (n : ℕ) : 0 < s₀ n := (Nat.succ_pos _).trans_le (le_max_left _ _)
  have hk : Tendsto k atTop atTop := tendsto_atTop_mono
    (fun n => (Nat.le_succ n).trans (le_max_left _ _)) tendsto_id
  have h4 := tendsto_pow_atTop (α := ℕ) (by norm_num : 4 ≠ 0)
  obtain ⟨j,hj,hrep⟩ := integral_repetitions d (fun i => Nat.mul_pos (Nat.succ_pos _) (hs₀ _))
  let r (m : ℕ) := j m + 1
  let s (m : ℕ) := s₀ (r m)
  have hr : Tendsto r atTop atTop := tendsto_atTop_mono (fun m => Nat.le_succ (j m)) hj
  have hs : Tendsto s atTop atTop := (hk.comp h4).comp hr
  refine ⟨R,B,r,s,hw.1,hw.2,fun m => hs₀ _,hr,hs,?_⟩
  let P := 2*(ccmRealExponentialMoment (1/2) (packet a)*ccmRealExponentialMoment (-(1/2)) (packet a))
  have hq : Tendsto (fun m : ℕ => Real.log (separatedPoleQuotient a R B (r m) (s m) : ℝ) /
      (d (j m):ℝ)^2) atTop (𝓝 P) := by
    apply (((hlim k (Eventually.of_forall fun n => le_max_right _ _)).comp h4).comp hr).congr
    intro m
    rw [separatedPoleQuotient,(sampledOrderQuotient_spec (hs₀ (r m)) _ _ _ _).2]
    exact fourth_power_normalization _ _ _
  let e (m : ℕ) := m^2/(d (j m))^2
  have hfinite : Tendsto (fun m : ℕ => (e m:ℝ)*
      Real.log (separatedPoleQuotient a R B (r m) (s m) : ℝ)/(m:ℝ)^2) atTop (𝓝 P) := by
    have h := hrep.mul hq
    rw [one_mul] at h
    apply h.congr fun m => ?_
    have hd : (d (j m) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (Nat.succ_pos (j m)) (hs₀ _)).ne'
    dsimp only [e]
    field_simp [hd]
  have hp := ((ray_moment_limit a (1/2)).mul (ray_moment_limit a (-(1/2)))).const_mul 2
  have h := (hfinite.sub hp).add (tendsto_splineDegree a)
  change Tendsto _ _ (𝓝 ((P-P)+integerProbe N a)) at h
  rw [sub_self,zero_add] at h
  apply h.congr fun m => ?_
  have hgen : (generator (m • a) : ℝ) ≠ 0 := by exact_mod_cast (contactGenerator_pos _ _ _).ne'
  have hunit : (separatedPoleQuotient a R B (r m) (s m) : ℝ) ≠ 0 := by
    exact_mod_cast (sampledOrderQuotient_spec (hs₀ (r m)) _ _ _ _).1.ne'
  rw [poleAdjustedGenerator,Rat.cast_div,Rat.cast_pow,Real.log_div hgen (pow_ne_zero _ hunit),Real.log_pow]
  change _ = (-degreeForm _ _ _ - (Real.log (generator (m • a) : ℝ) -
    (e m:ℝ)*Real.log (separatedPoleQuotient a R B (r m) (s m) : ℝ))) / (m : ℝ)^2
  simp only [radius,logRadius,div_mul_div_comm,← sq]
  ring

#print axioms separatedPoleQuotient_effective
#print axioms integerProbe_from_separated_orders_and_jets

end GaloisForLFunctions.CountingHolography.Sections
