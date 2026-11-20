import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheHalfAbscissaOfTheBalancedCompositeRemainder
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOuterCellsOfTheFractionalPrimeMidpoint
import GaloisForLFunctions.RHTower.CausalMobiusThetaPrimorialInnovation

/-!
# The fractional probe of the corrected composite price

Apply the complementary kernels of Meiners and Gnewuch, §3.5, to the
full-log proper-power atoms after subtracting the discrete derivatives
of the square and cube corrections. The integral recovers the corrected
price exactly. Its order can vary arbitrarily with the center.
-/

noncomputable section
open Finset Filter MeasureTheory
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The exact square and cube correction charged at one integer. -/
def compositeRootPayment (k : ℕ) : ℝ :=
    2*((k:ℝ)^(1/2:ℝ)-((k-1:ℕ):ℝ)^(1/2:ℝ)) +
    3*((k:ℝ)^(1/3:ℝ)-((k-1:ℕ):ℝ)^(1/3:ℝ))

/-- Weight at an integer after paying the two deterministic root increments. -/
def correctedCompositeAtom (m k : ℕ) : ℝ := purePowerLog m k-compositeRootPayment k

/-- The beta-normalized fractional observation with coprimality center m. -/
def correctedCompositeProbe (m n : ℕ) (b : ℝ) : ℝ :=
  (∫ t : ℝ, midpointFractionalTest n b t *
    field (Ioc (2*n) (4*n)) Nat.cast (correctedCompositeAtom m) (b-1) t) /
      ProbabilityTheory.beta (1-b) b

private theorem paired_octave (w : ℕ → ℝ) (n : ℕ) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, midpointFractionalTest n b t *
      field (Ioc (2*n) (4*n)) Nat.cast w (b-1) t) / ProbabilityTheory.beta (1-b) b =
      (∑ k ∈ Ioc (2*n) (3*n), w k) - ∑ k ∈ Ioc (3*n) (4*n), w k := by
  let S := Ioc (2*n) (4*n)
  let B := ProbabilityTheory.beta (1-b) b
  have hB : 0<B := ProbabilityTheory.beta_pos (sub_pos.mpr hb.2) hb.1
  have hi (j : ℕ) : Integrable (fun t => cutPower (-b) (t-j)*field S Nat.cast w (b-1) t) := by
    simpa only [show 1-b-1= -b by ring] using integrable_pairing S Nat.cast w (sub_pos.mpr hb.2) hb.1 (j:ℝ)
  have ev (j : ℕ) : (∫ t, cutPower (-b) (t-j)*field S Nat.cast w (b-1) t) =
      B*∑ k ∈ S.filter (j < ·), w k := by
    simpa only [B,sum_filter,Nat.cast_lt] using complementary_tail S Nat.cast w hb (j:ℝ)
  have hL : S.filter (2*n < ·)=S := filter_true_of_mem fun _ hk => (mem_Ioc.mp hk).1
  have hU : S.filter (3*n < ·)=Ioc (3*n) (4*n) := by
    ext k
    simp only [S,mem_filter,mem_Ioc]
    omega
  apply (div_eq_iff hB.ne').mpr
  simp only [midpointFractionalTest,sub_mul,mul_assoc]
  rw [integral_sub (hi (2*n)) ((hi (3*n)).const_mul 2),integral_const_mul,ev,ev,hL,hU]
  dsimp only [S,B]
  rw [←sum_Ioc_consecutive w (by omega : 2*n≤3*n) (by omega : 3*n≤4*n)]
  ring

private theorem corrected_atom_mass (m : ℕ) {a b : ℕ} (hab : a≤b) :
    ∑ k ∈ Ioc a b, correctedCompositeAtom m k =
      (fullLogProperPrefix m b-fullLogProperPrefix m a) -
        2*((b:ℝ)^(1/2:ℝ)-(a:ℝ)^(1/2:ℝ)) - 3*((b:ℝ)^(1/3:ℝ)-(a:ℝ)^(1/3:ℝ)) := by
  have hp : ∑ k ∈ Ioc a b, purePowerLog m k=fullLogProperPrefix m b-fullLogProperPrefix m a := by
    simp only [fullLogProperPrefix,Nat.floor_natCast]
    exact eq_sub_of_add_eq' (sum_Ioc_consecutive _ (Nat.zero_le a) hab)
  unfold correctedCompositeAtom compositeRootPayment
  rw [sum_sub_distrib,hp,sum_add_distrib,←mul_sum,←mul_sum,_root_.RHTower.sum_Ioc_sub_eq (fun k : ℕ => (k:ℝ)^(1/2:ℝ)) hab,
    _root_.RHTower.sum_Ioc_sub_eq (fun k : ℕ => (k:ℝ)^(1/3:ℝ)) hab]
  ring

private theorem evaluation_at_three_cuts (m n : ℕ) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    correctedCompositeProbe m n b =
      2*fullLogProperPrefix m (3*n:ℕ)-fullLogProperPrefix m (2*n:ℕ)-fullLogProperPrefix m (4*n:ℕ) -
        2*midpointPowerGap (1/2)*(n:ℝ)^(1/2:ℝ) - 3*midpointPowerGap (1/3)*(n:ℝ)^(1/3:ℝ) := by
  have hs := real_midpoint_of_power (1/2) (Nat.cast_nonneg (α:=ℝ) n)
  have hc := real_midpoint_of_power (1/3) (Nat.cast_nonneg (α:=ℝ) n)
  rw [correctedCompositeProbe,paired_octave _ _ hb,corrected_atom_mass m (by omega : 2*n≤3*n),
    corrected_atom_mass m (by omega : 3*n≤4*n)]
  simp only [Nat.cast_mul,Nat.cast_ofNat,realMidpointObservation] at hs hc ⊢
  linarith only [hs,hc]

/-- With the observed center as the coprimality center, the normalized
integral is identically the genuinely corrected arithmetic price. -/
theorem fractional_probe_recovers_corrected_composite {n : ℕ} (hn : 1≤n) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    correctedCompositeProbe n n b=correctedBalancedCompositePrice n := by
  rw [evaluation_at_three_cuts _ _ hb,correctedBalancedCompositePrice,squareCenteredCompositePrice,
    composite_midpoint_minus_prime hn,Real.sqrt_eq_rpow]

/-- A single unrestricted row reads the corrected real prefix at the
three integer cuts, for every center and every fractional order. -/
theorem fractional_probe_recovers_fixed_prefix (n : ℕ) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    correctedCompositeProbe 1 n b=realMidpointObservation correctedProperPrefix n := by
  rw [evaluation_at_three_cuts _ _ hb]
  have hs := real_midpoint_of_power (1/2) (Nat.cast_nonneg (α:=ℝ) n)
  have hc := real_midpoint_of_power (1/3) (Nat.cast_nonneg (α:=ℝ) n)
  simp only [Nat.cast_mul,Nat.cast_ofNat,realMidpointObservation,correctedProperPrefix] at hs hc ⊢
  linarith only [hs,hc]

/-- Independently choosing the order at every integer preserves the
exact one-sided exponent, even if the orders approach zero or one. -/
theorem varying_order_composite_probe_spectrum (β : ℕ → Set.Ioo (0:ℝ) 1) (b : ℝ) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ n : ℕ, 1≤n →
      correctedCompositeProbe n n (β n)≤A*(n:ℝ)^t) ↔ _root_.RHTower.zetaZeroAbscissa≤2*b := by
  rw [←corrected_composite_all_power_cutoffs b]
  constructor <;> intro h t hbt ht <;> obtain ⟨A,hA⟩ := h t hbt ht <;> refine ⟨A,fun n hn => ?_⟩
  · simpa only [fractional_probe_recovers_corrected_composite hn (β n).2] using hA n hn
  · rw [fractional_probe_recovers_corrected_composite hn (β n).2]
    exact hA n hn

/-- No choice of order suppresses the endpoint excursions, even for the
single row of atoms with the coprimality restriction removed. -/
theorem fixed_composite_probe_exceeds_every_quarter_power (β : ℕ → Set.Ioo (0:ℝ) 1) (A : ℝ) :
    ∃ᶠ n : ℕ in atTop, A*(n:ℝ)^(1/4:ℝ)<correctedCompositeProbe 1 n (β n) := by
  obtain ⟨C,_,hC⟩ := corrected_composite_price_reads_the_prefix (t:=1/4) le_rfl
  apply ((unbounded_quarter_power_composite_surplus (A+C)).and_eventually (eventually_ge_atTop 1)).mono
  rintro n ⟨he,hn⟩
  rw [fractional_probe_recovers_fixed_prefix n (β n).2]
  linarith only [he,(abs_le.mp (hC n hn)).2]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
