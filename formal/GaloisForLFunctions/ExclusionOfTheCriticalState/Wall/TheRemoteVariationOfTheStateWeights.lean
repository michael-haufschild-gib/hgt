import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IntegerQuadratureOnOneLogarithmicCell
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfThePrimeWave
import GaloisForLFunctions.RHTower.CausalMobiusThetaStability
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEnvelope
import GaloisForLFunctions.RHTower.Sieve.CharacterWindowMass

/-!
# The remote variation of the state weights

Start the centered Mangoldt prefix at the right edge of any initial interval.
Confinement bounds both the Abel endpoint and the entire rising variation
beyond a remote cutoff, uniformly in that starting edge.
-/

noncomputable section
open MeasureTheory Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry

/-- The prefix beyond the starting edge, including the integer reference. -/
def centeredAbelPrefix (b j : ℕ) : ℝ := ∑ n ∈ Finset.Ioc b j, (vonMangoldt n-1)

/-- Removing an initial interval subtracts its prefix at both endpoints. -/
theorem centeredAbelPrefix_sub {q b j : ℕ} (hqb : q ≤ b) (hbj : b ≤ j) :
    centeredAbelPrefix b j = centeredAbelPrefix q j-centeredAbelPrefix q b := by
  have h := Finset.sum_Ioc_consecutive (fun n : ℕ => vonMangoldt n-1) hqb hbj
  unfold centeredAbelPrefix
  linarith only [h]

/-- Discrete summation by parts on any subinterval of the complement.
Both endpoints use the prefix based at the original edge. -/
theorem centeredAbelPrefix_by_parts (w : ℕ → ℝ) {b N L : ℕ} (hbN : b ≤ N) (hNL : N ≤ L) :
    (∑ n ∈ Finset.Ioc N L, (vonMangoldt n-1)*w n) =
      w L*centeredAbelPrefix b L-w N*centeredAbelPrefix b N+
        ∑ j ∈ Finset.Ico N L, centeredAbelPrefix b j*(w j-w (j+1)) := by
  induction L, hNL using Nat.le_induction with
  | base => simp
  | succ L hNL ih =>
    have hstep : centeredAbelPrefix b (L+1) = centeredAbelPrefix b L+(vonMangoldt (L+1)-1) :=
      Finset.sum_Ioc_succ_top (hbN.trans hNL) _
    rw [Finset.sum_Ioc_succ_top hNL,ih,Finset.sum_Ico_succ_top hNL,hstep]
    ring

private theorem abs_centeredAbelPrefix {b j : ℕ} (hb : b ≤ j) (hj : 1 ≤ j) :
    |centeredAbelPrefix b j| ≤ 6*(j:ℝ) := by
  have hbj : (b:ℝ) ≤ j := by exact_mod_cast hb
  have hψ := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc hbj
  simp only [Nat.floor_natCast] at hψ
  have hbound := _root_.RiemannGaussian.chebyshevPsi_le_six_mul_self_of_one_le
    (by exact_mod_cast hj : (1:ℝ) ≤ j)
  have hn : 0 ≤ ∑ n ∈ Finset.Ioc b j, vonMangoldt n := Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  rw [centeredAbelPrefix,Finset.sum_sub_distrib,Finset.sum_const, nsmul_eq_mul,mul_one,
    Nat.card_Ioc,Nat.cast_sub hb,abs_le]
  constructor
  · linarith only [hn,Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) j]
  · linarith only [hψ,hbound,Chebyshev.psi_nonneg (b:ℝ),hbj]

private theorem confined_atom_majorant {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ y, |Φ y| ≤ C*Real.exp (2*y)) (m t : ℝ) {x : ℝ} (hx : 0 < x) :
    |m*continuousIntegerAtom Φ x t| ≤ (|m| *C*Real.exp (2*t))/(x^2*Real.sqrt x) := by
  rw [continuousIntegerAtom,abs_mul,abs_mul,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc _ ≤ |m| *((Real.sqrt x)⁻¹*(C*Real.exp (2*(t-Real.log x)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb _) (by positivity)) (abs_nonneg _)
       _ = _ := by
          rw [mul_sub,Real.exp_sub,two_mul (Real.log x),Real.exp_add,Real.exp_log hx]
          ring

/-- Absolute Abel endpoint and positive rises at a common prefix. The second
bound sums even when the state oscillates arbitrarily fast on the remote ray. -/
theorem confined_state_remote_abel {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hΦ : ∀ y, |Φ y| ≤ C*Real.exp (2*y)) (m t : ℝ) {b N : ℕ}
    (hbN : b ≤ N) (hN : 1 ≤ N) :
    let w := fun j : ℕ => m*continuousIntegerAtom Φ j t
    let loss := fun j : ℕ => |centeredAbelPrefix b j| *max (w (j+1)-w j) 0
    let E := |m| *C*Real.exp (2*t)
    (∀ j : ℕ, N ≤ j → |w j*centeredAbelPrefix b j| ≤ 6*E*(j:ℝ)^(-(3/2:ℝ))) ∧
    Summable (fun k : ℕ => loss (N+1+k)) ∧
      (∑' k : ℕ, loss (N+1+k)) ≤ 24*E*(Real.sqrt N)⁻¹ := by
  let w := fun j : ℕ => m*continuousIntegerAtom Φ j t
  let E := |m| *C*Real.exp (2*t)
  let loss := fun j : ℕ => |centeredAbelPrefix b j| *max (w (j+1)-w j) 0
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hw {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
      |w j| ≤ E/((i:ℝ)^2*Real.sqrt i) := by
    have hi0 : 0 < (i:ℝ) := by exact_mod_cast hi
    have hij' : (i:ℝ) ≤ j := by exact_mod_cast hij
    refine (confined_atom_majorant hΦ m t (hi0.trans_le hij')).trans ?_
    apply div_le_div_of_nonneg_left hE (by positivity)
    exact mul_le_mul (pow_le_pow_left₀ hi0.le hij' _) (Real.sqrt_le_sqrt hij')
      (Real.sqrt_nonneg _) (sq_nonneg _)
  have hrate {j : ℕ} (hj : 1 ≤ j) :
      6*(j:ℝ)*(E/((j:ℝ)^2*Real.sqrt j)) = 6*E*(j:ℝ)^(-(3/2:ℝ)) := by
    have hj0 : 0 < (j:ℝ) := by exact_mod_cast hj
    rw [_root_.RHTower.rpow_neg_three_halves_eq_inv_mul_sqrt hj0]
    field_simp [hj0.ne', (Real.sqrt_pos.mpr hj0).ne']
  have hpoint {j : ℕ} (hj : N ≤ j) :
      loss j ≤ 12*E*(j:ℝ)^(-(3/2:ℝ)) := by
    have hj1 := hN.trans hj
    let p := E/((j:ℝ)^2*Real.sqrt j)
    have hp : 0 ≤ p := by dsimp only [p]; positivity
    have hdiff : max (w (j+1)-w j) 0 ≤ p+p := max_le
      ((le_abs_self _).trans ((abs_sub ..).trans (add_le_add (hw hj1 (Nat.le_succ _)) (hw hj1 le_rfl))))
      (add_nonneg hp hp)
    calc loss j ≤ (6*(j:ℝ))*(p+p) := mul_le_mul (abs_centeredAbelPrefix (hbN.trans hj) hj1)
           hdiff (le_max_right _ _) (by positivity)
         _ = _ := by dsimp only [p]; rw [mul_add,hrate hj1]; ring
  obtain ⟨hs,hsum⟩ := _root_.RHTower.tsum_shift_rpow_neg_three_halves_le hN
  have hdom := hs.mul_left (12*E)
  have hle (k : ℕ) := hpoint (j := N+1+k) (by omega)
  have hnon (k : ℕ) : 0 ≤ loss (N+1+k) := mul_nonneg (abs_nonneg _) (le_max_right _ _)
  have hsumloss := Summable.of_nonneg_of_le hnon hle hdom
  refine ⟨fun j hj => ?_,hsumloss,(hsumloss.tsum_le_tsum hle hdom).trans ?_⟩
  · change |w j*centeredAbelPrefix b j| ≤ _
    rw [abs_mul,mul_comm |w j|]
    exact (mul_le_mul (abs_centeredAbelPrefix (hbN.trans hj) (hN.trans hj))
      (hw (hN.trans hj) le_rfl) (abs_nonneg _) (by positivity)).trans_eq (hrate (hN.trans hj))
  · rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 12*E)).trans_eq (by ring)

/-- The same forced state has these bounds at every time and every starting edge. -/
theorem riemannHypothesis_or_remote_abel_variation : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧
      ∀ (t : ℝ) (b N : ℕ), b ≤ N → 1 ≤ N →
        let w := fun j : ℕ => (∫ y, Φ y)*continuousIntegerAtom Φ j t
        let loss := fun j : ℕ => |centeredAbelPrefix b j| *max (w (j+1)-w j) 0
        (∀ j : ℕ, N ≤ j → |w j*centeredAbelPrefix b j| ≤ B*Real.exp (2*t)*(j:ℝ)^(-(3/2:ℝ))) ∧
        Summable (fun k : ℕ => loss (N+1+k)) ∧
          (∑' k : ℕ, loss (N+1+k)) ≤ B*Real.exp (2*t)*(Real.sqrt N)⁻¹ := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hΦ⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  let m := ∫ y, Φ y
  refine Or.inr ⟨W₀,F,Φ,24*(|m| *C),hW,ht,hF,hc,he,by positivity,fun t b N hbN hN => ?_⟩
  obtain ⟨hend,hs,hbound⟩ := confined_state_remote_abel hC hΦ m t hbN hN
  refine ⟨fun j hj => (hend j hj).trans ?_,hs,hbound.trans_eq (by ring)⟩
  have hnon : 0 ≤ |m| *C*Real.exp (2*t)*(j:ℝ)^(-(3/2:ℝ)) := by positivity
  linarith only [hnon]

/-- Rising Abel loss beyond exp(6t), with the prefix based at the critical
window edge. The cutoff also covers the edge for small or negative times. -/
def remoteRisingAbelLoss (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  let b := ⌊Real.exp t+Real.exp (t/2)*Real.sqrt t⌋₊
  let N := max b (max 1 ⌈Real.exp (6*t)⌉₊)
  let w := fun j : ℕ => (∫ y, Φ y)*continuousIntegerAtom Φ j t
  ∑' k : ℕ, let j := N+1+k
            |centeredAbelPrefix b j| *max (w (j+1)-w j) 0

private theorem measurable_remoteRisingAbelLoss {Φ : ℝ → ℝ} (hc : Continuous Φ) :
    Measurable (remoteRisingAbelLoss Φ) := by
  let b := fun t : ℝ => ⌊Real.exp t+Real.exp (t/2)*Real.sqrt t⌋₊
  let N := fun t : ℝ => max (b t) (max 1 ⌈Real.exp (6*t)⌉₊)
  let w := fun (j : ℕ) (t : ℝ) => (∫ y, Φ y)*continuousIntegerAtom Φ j t
  have hb : Measurable b := by dsimp only [b]; fun_prop
  have hN : Measurable N := by dsimp only [N]; fun_prop
  have hw (j : ℕ) : Measurable (w j) := by
    dsimp only [w,continuousIntegerAtom]
    exact measurable_const.mul (measurable_const.mul (hc.measurable.comp (by fun_prop)))
  apply Measurable.tsum
  intro k
  let idx := fun t : ℝ => N t+1+k
  have hi : Measurable idx := by dsimp only [idx]; fun_prop
  have hP : Measurable (fun t => centeredAbelPrefix (b t) (idx t)) :=
    (measurable_of_countable (f := fun p : ℕ × ℕ => centeredAbelPrefix p.1 p.2)).comp (hb.prodMk hi)
  have hw' {j : ℝ → ℕ} (hj : Measurable j) : Measurable (fun t => w (j t) t) :=
    (measurable_from_prod_countable_right (f := fun p : ℕ × ℝ => w p.1 p.2) hw).comp (hj.prodMk measurable_id)
  exact hP.abs.mul (((hw' (j := fun t => idx t+1) (by fun_prop)).sub (hw' hi)).max measurable_const)

/-- On every measurable part of the original late test, including its full
complement outside any favorable set, the remote rising cost decays
exponentially in the test time. -/
theorem criticalState_remote_rising_test {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T : ℝ) (A : Set ℝ), MeasurableSet A →
      let f := fun t => remoteRisingAbelLoss Φ t*fractionalPrimeTest (T-t)
      IntegrableOn f (A ∩ Set.Ioi (T/6)) ∧ (∫ t in A ∩ Set.Ioi (T/6), f t) ≤ B*Real.exp (-T/6) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hΦ⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ y, Φ y
  let B := 24*(|m| *C)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B,hB,fun T A _hA => ?_⟩
  let f := fun t => remoteRisingAbelLoss Φ t*fractionalPrimeTest (T-t)
  let g := fun t : ℝ => B*Real.exp ((-1)*t)
  have hbnd (t : ℝ) : 0 ≤ remoteRisingAbelLoss Φ t ∧ remoteRisingAbelLoss Φ t ≤ g t := by
    let b := ⌊Real.exp t+Real.exp (t/2)*Real.sqrt t⌋₊
    let N : ℕ := max b (max 1 ⌈Real.exp (6*t)⌉₊)
    have hN : 1 ≤ N := (le_max_left ..).trans (le_max_right ..)
    have hexp : Real.exp (6*t) ≤ N := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈Real.exp (6*t)⌉₊ ≤ N from (le_max_right ..).trans (le_max_right ..)))
    have hroot : Real.exp (3*t) ≤ Real.sqrt N := by
      rw [show 3*t = (6*t)/2 by ring,Real.exp_half]; exact Real.sqrt_le_sqrt hexp
    have hh := (confined_state_remote_abel hC hΦ m t (le_max_left b _) hN).2.2
    refine ⟨tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (le_max_right _ _),hh.trans ?_⟩
    calc _ ≤ (24*(|m| *C*Real.exp (2*t)))*(Real.exp (3*t))⁻¹ :=
             mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) hroot) (by positivity)
         _ = (24*(|m| *C))*(Real.exp (2*t)*(Real.exp (3*t))⁻¹) := by ring
         _ = g t := by
           rw [← Real.exp_neg,← Real.exp_add,show 2*t+ -(3*t) = (-1)*t by ring]
  have h0 (t : ℝ) : 0 ≤ f t := mul_nonneg (hbnd t).1 (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))
  have hle (t : ℝ) : f t ≤ g t := (mul_le_of_le_one_right (hbnd t).1
    ((le_abs_self _).trans (fractionalPrimeTest_bounds _).1)).trans (hbnd t).2
  have hgi : IntegrableOn g (Set.Ioi (T/6)) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) _).const_mul _
  have hfi : IntegrableOn f (Set.Ioi (T/6)) := hgi.mono'
    ((measurable_remoteRisingAbelLoss hc).mul (measurable_fractionalPrimeTest.comp
      (by fun_prop))).aestronglyMeasurable (Eventually.of_forall fun t => (Real.norm_of_nonneg (h0 t)).le.trans (hle t))
  refine ⟨hfi.mono_set Set.inter_subset_right,?_⟩
  calc (∫ t in A ∩ Set.Ioi (T/6), f t) ≤ ∫ t in Set.Ioi (T/6), f t :=
         setIntegral_mono_set hfi (Eventually.of_forall h0) (Eventually.of_forall fun _ ht => ht.2)
       _ ≤ ∫ t in Set.Ioi (T/6), g t := integral_mono_ae hfi hgi (Eventually.of_forall hle)
       _ = _ := by dsimp only [g]; rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0)]
                   simp only [neg_one_mul,div_neg,div_one,neg_neg,neg_div]

#print axioms criticalState_remote_rising_test
#print axioms riemannHypothesis_or_remote_abel_variation
end GaloisForLFunctions.ExclusionOfTheCriticalState
