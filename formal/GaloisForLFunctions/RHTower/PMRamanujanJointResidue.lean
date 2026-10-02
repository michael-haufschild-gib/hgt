import GaloisForLFunctions.RHTower.PMRamanujanBandResidue
import GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal

/-!
# Joint-residue drift cancellation at natural Ramanujan cutoffs

The actual cofactor residue has an exact joint drift: summing over a
product fibre leaves the reciprocal-power Möbius coefficient. Remove
that linear spatial mode before taking Hilbert norms. Each resulting
atom has finite anchored energy, and the full finite centered prefix and
complete natural band are reconstructed with their product cutoffs intact.

No uniform energy bound on the signed sum of these atoms is asserted.
-/

open ArithmeticFunction Finset
open scoped BigOperators
noncomputable section
namespace RHTower


private theorem pm_joint_reindex (F : ℕ → ℕ → ℕ → ℂ) (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, ∑ y ∈ x.2.divisorsAntidiagonal,
      F x.1 y.1 y.2) =
    ∑ x ∈ n.divisorsAntidiagonal, ∑ y ∈ x.1.divisorsAntidiagonal,
      F y.1 x.2 y.2 := by
  simp only [sum_sigma']
  apply sum_nbij'
    (fun ⟨⟨d, _r⟩, ⟨t, m⟩⟩ => ⟨(d*m,t),(d,m)⟩)
    (fun ⟨⟨_k,t⟩, ⟨d,m⟩⟩ => ⟨(d,t*m),(t,m)⟩) <;>
    aesop (add simp [mul_assoc, mul_comm, mul_left_comm])

/-- Actual joint residue, with its reciprocal power retained. -/
def pmRamanujanJointResidue (ε : ℝ) (d r : ℕ) : ℂ :=
  pmPowerDampedRamanujanWeight ε d *
    (((r : ℝ)^(-1-ε)*pmRamanujanBandResidue ε d r : ℝ) : ℂ)

theorem pmRamanujanJointResidue_eq {ε : ℝ} (hε : 0 < ε) (d r : ℕ) :
    pmRamanujanJointResidue ε d r =
      ∑ x ∈ r.divisorsAntidiagonal,
        (moebius x.1 : ℂ)*(((x.1 : ℝ)^(-1-ε) : ℝ) : ℂ)*
          ((moebius x.2 : ℂ)*pmPowerDampedRamanujanWeight ε (d*x.2)) := by
  unfold pmRamanujanJointResidue pmRamanujanBandResidue
  rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hp : (r : ℝ)^(-1-ε) = (x.1 : ℝ)^(-1-ε)*(x.2 : ℝ)^(-1-ε) := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg x.1) (Nat.cast_nonneg x.2)]
  rw [pmRamanujanBandSquarefree_actual hε d x.2, hp]
  push_cast
  simp only [ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast]
  ring

theorem pmRamanujanJointResidue_drift {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, pmRamanujanJointResidue ε x.1 x.2) =
      pmPowerDampedRamanujanWeight ε 1 * (moebius n : ℂ)*
        (((n : ℝ)^(-1-ε) : ℝ) : ℂ) := by
  simp_rw [pmRamanujanJointResidue_eq hε]
  rw [pm_joint_reindex (fun d t m => (moebius t : ℂ)*(((t : ℝ)^(-1-ε) : ℝ) : ℂ)*
    ((moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m))) n]
  have hs (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) :
      (∑ y ∈ x.1.divisorsAntidiagonal,
        (moebius x.2 : ℂ)*(((x.2 : ℝ)^(-1-ε) : ℝ) : ℂ)*
          ((moebius y.2 : ℂ)*pmPowerDampedRamanujanWeight ε (y.1*y.2))) =
      (moebius x.2 : ℂ)*(((x.2 : ℝ)^(-1-ε) : ℝ) : ℂ)*
        pmPowerDampedRamanujanWeight ε x.1 * (if x.1=1 then 1 else 0) := by
    rw [← pm_mobius_antidiagonal_sum x.1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [(Nat.mem_divisorsAntidiagonal.mp hy).1]
    ring
  rw [Finset.sum_congr rfl hs]
  by_cases hn : n=0
  · subst n; simp
  rw [Finset.sum_eq_single (1,n)]
  · simp; ring
  · intro x hx hxn
    have hx1 : x.1 ≠ 1 := by
      intro he
      have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [he, one_mul] at hm
      exact hxn (Prod.ext he hm)
    simp [hx1]
  · intro h
    exact False.elim (h (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩))


/-- Bounded spatial atom: the linear drift is removed before taking a norm. -/
def pmRamanujanJointAtom (ε : ℝ) (l N : ℕ) : ℂ :=
  -∑ x ∈ l.divisorsAntidiagonal, pmRamanujanJointResidue ε x.1 x.2 *
    (x.1 : ℂ)*((Int.fract ((N : ℝ)/(x.1 : ℝ)) : ℝ) : ℂ)

/-- Exact finite clock, retaining the product cutoff. -/
def pmRamanujanJointClock (ε : ℝ) (Q l : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 (Q/l), (((k : ℝ)^(-1-ε) : ℝ) : ℂ)

theorem pmRamanujanJointAtom_norm_le (ε : ℝ) (l N : ℕ) :
    ‖pmRamanujanJointAtom ε l N‖ ≤
      ∑ x ∈ l.divisorsAntidiagonal, ‖pmRamanujanJointResidue ε x.1 x.2‖*(x.1 : ℝ) := by
  rw [pmRamanujanJointAtom, norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro x hx
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  exact mul_le_of_le_one_right (by positivity) (norm_fract_le _)

theorem pmRamanujanJointAtom_eq_centered {ε : ℝ} (hε : 0 < ε) (l N : ℕ) :
    pmRamanujanJointAtom ε l N =
      (∑ x ∈ l.divisorsAntidiagonal, pmRamanujanJointResidue ε x.1 x.2 *
        (x.1 : ℂ)*((N/x.1 : ℕ) : ℂ)) -
      pmPowerDampedRamanujanWeight ε 1 * (moebius l : ℂ)*
        (((l : ℝ)^(-1-ε) : ℝ) : ℂ)*(N : ℂ) := by
  rw [← pmRamanujanJointResidue_drift hε, Finset.sum_mul, ← Finset.sum_sub_distrib]
  unfold pmRamanujanJointAtom
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hx0 : (x.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne'
  rw [pm_nat_div_eq_sub_fract]
  push_cast
  field_simp
  ring

theorem pmPowerDampedRamanujanCumulativePrefix_eq_joint {ε : ℝ} (hε : 0 < ε)
    (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε Q N =
      ∑ l ∈ Icc 1 (Q+1), pmRamanujanJointClock ε (Q+1) l *
        pmRamanujanJointAtom ε l N := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract hε]
  simp only [pmRamanujanJointAtom, mul_neg, Finset.sum_neg_distrib]
  congr 1
  symm
  calc
    _ = ∑ l ∈ Icc 1 (Q+1), ∑ x ∈ l.divisorsAntidiagonal,
        pmRamanujanJointClock ε (Q+1) (x.1*x.2) *
          pmRamanujanJointResidue ε x.1 x.2 * (x.1 : ℂ)*
            ((Int.fract ((N : ℝ)/(x.1 : ℝ)) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
      ring
    _ = ∑ d ∈ Icc 1 (Q+1), ∑ r ∈ Icc 1 ((Q+1)/d),
        pmRamanujanJointClock ε (Q+1) (d*r) * pmRamanujanJointResidue ε d r *
          (d : ℂ)*((Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ) :=
      Sieve.sum_Icc_divisorsAntidiagonal_swap
        (fun d r => pmRamanujanJointClock ε (Q+1) (d*r) *
          pmRamanujanJointResidue ε d r * (d : ℂ)*
            ((Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ)) (Q+1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [pmPowerDampedRamanujanCofactor_eq_residue hε]
      simp only [pmRamanujanJointClock, pmRamanujanJointResidue,
        Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul,
        Nat.div_div_eq_div_mul]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro k hk
      ring


theorem summable_pmRamanujanJointAtom_energy (ε : ℝ) (l : ℕ) :
    Summable (fun N : ℕ => ‖pmRamanujanJointAtom ε l N‖^2 /
      ((N : ℝ)*((N : ℝ)+1))) := by
  let B := ∑ x ∈ l.divisorsAntidiagonal,
    ‖pmRamanujanJointResidue ε x.1 x.2‖*(x.1 : ℝ)
  apply Summable.of_nonneg_of_le (fun N => by positivity) _
    (hasSum_pm_reciprocal_weight.summable.mul_left (B^2))
  intro N
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (pmRamanujanJointAtom_norm_le ε l N) 2)
    (by positivity)

private theorem joint_prefix_primitive {ε : ℝ} (hε : 0 < ε) {Q : ℕ}
    (hQ : 1 ≤ Q) (N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε (Q-1) N =
      (∑ q ∈ Icc 1 Q, pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitive q N) -
        pmPowerDampedDivisorDensity ε * N := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_floor hε,
    Nat.sub_add_cancel hQ, ← pmPowerDampedRamanujanCofactor_cumulative,
    Finset.sum_comm]
  simp only [pmRamanujanPrimitive, Finset.mul_sum]

/-- Complete natural bands are finite sums of bounded joint atoms. -/
theorem pmRamanujanDenominatorBand_eq_joint {ε : ℝ} (hε : 0 < ε)
    {X Y : ℕ} (hX : 1 ≤ X) (hXY : X ≤ Y) (N : ℕ) :
    pmRamanujanDenominatorBand ε X Y N =
      (∑ l ∈ Icc 1 Y, pmRamanujanJointClock ε Y l * pmRamanujanJointAtom ε l N) -
        ∑ l ∈ Icc 1 X, pmRamanujanJointClock ε X l * pmRamanujanJointAtom ε l N := by
  have hY : 1 ≤ Y := hX.trans hXY
  have hs : Icc 1 X ⊆ Icc 1 Y := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hXY⟩
  have hdiff : Icc 1 Y \ Icc 1 X = Ioc X Y := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hb : pmRamanujanDenominatorBand ε X Y N =
      pmPowerDampedRamanujanCumulativePrefix ε (Y-1) N -
        pmPowerDampedRamanujanCumulativePrefix ε (X-1) N := by
    rw [joint_prefix_primitive hε hY, joint_prefix_primitive hε hX]
    unfold pmRamanujanDenominatorBand
    rw [← hdiff, Finset.sum_sdiff_eq_sub hs]
    ring
  rw [hb, pmPowerDampedRamanujanCumulativePrefix_eq_joint hε,
    pmPowerDampedRamanujanCumulativePrefix_eq_joint hε,
    Nat.sub_add_cancel hX, Nat.sub_add_cancel hY]

end RHTower
