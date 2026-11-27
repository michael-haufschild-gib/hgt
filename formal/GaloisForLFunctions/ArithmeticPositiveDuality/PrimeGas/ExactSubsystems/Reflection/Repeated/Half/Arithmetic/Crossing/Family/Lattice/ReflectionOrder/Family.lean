import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Occupations
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Jet

/-! # Prime preparations with arbitrary odd reflection order -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder

open Finset Real Filter
open scoped Topology
open _root_.HTGeometry (finiteGibbsStateWeight)
open PrimeCalibration (log_pos_prime)
open PrimeCalibration.Multiplicity (gibbs_defect lawDefect)

def Carrier : ℕ → Type
  | 0 => Unit
  | n+1 => Four (Carrier n)

instance finiteCarrier : (n : ℕ) → Fintype (Carrier n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI : Fintype (Carrier n) := finiteCarrier n
           inferInstanceAs (Fintype (Four (Carrier n)))

def width (n : ℕ) := 2*n+1

def shells : (n : ℕ) → Carrier n → ℕ
  | 0 => fun _ => 0
  | n+1 => occupations (shells n) (width n)

private def offsets (n : ℕ) (i : Carrier n) : ℝ := (shells n i : ℝ)-(width n : ℝ)/2

private theorem width_succ (n : ℕ) : width (n+1)=width n+2 := by unfold width; omega

theorem shell_bound (n : ℕ) : ∀ i, shells n i≤width n := by
  induction n with
  | zero => intro i; exact Nat.zero_le _
  | succ n ih => rw [width_succ]; exact (lift_grid _ _ ih).1

theorem shell_size (n : ℕ) : Fintype.card (Carrier n)=4^n := by
  induction n with
  | zero => exact Fintype.card_unit
  | succ n ih =>
    change Fintype.card (Four (Carrier n))=_
    simp only [Four,Fintype.card_sum,ih,pow_succ]
    ring

private theorem step (n : ℕ) : offsets (n+1)=branches (offsets n) 1 := by
  change (fun x => (occupations (shells n) (width n) x : ℝ)-(width (n+1) : ℝ)/2)=_
  rw [width_succ]
  exact lift_raw _ _ (shell_bound n)

private theorem center (n : ℕ) : centered (levels (shells (n+1)))=offsets (n+1) := by
  funext i
  letI : Nonempty (Carrier (n+1)) := ⟨i⟩
  apply center_grid _ (width (n+1))
  rw [width_succ]
  exact (lift_grid _ _ (shell_bound n)).2

private theorem trace_eq (n : ℕ) (t : ℝ) :
    oddTrace (offsets n) t=multiplier 1 t^n*(exp (t*(-1/2))-exp (t*(1/2))) := by
  induction n with
  | zero =>
    have base : offsets 0=fun _ => -(1/2 : ℝ) := by funext i; norm_num [offsets,shells,width]
    simp only [oddTrace,base,sum_const,card_univ,shell_size,pow_zero,one_nsmul,one_mul,
      oddTerm,neg_div,mul_neg,neg_mul,neg_neg]
  | succ n ih =>
    rw [step]
    calc
      _ = multiplier 1 t*oddTrace (offsets n) t := branch_response (offsets n) 1 t
      _ = _ := by rw [ih,pow_succ]; ring

/-- Four branches at each step yield an asymmetric packet whose sole tie
is at the isometry line. Its contact order is 2n+3 after n+1 lifts. -/
theorem shell_trace (n : ℕ) (t : ℝ) :
    oddTrace (centered (levels (shells (n+1)))) t=
      multiplier 1 t^(n+1)*(exp (t*(-1/2))-exp (t*(1/2))) := by
  rw [center,trace_eq]

private theorem seed_limit :
    Tendsto (fun t : ℝ => (exp (t*(-1/2))-exp (t*(1/2)))/t) (𝓝[≠] 0) (𝓝 (-1)) := by
  have lin (a : ℝ) : HasDerivAt (fun t : ℝ => t*a) a 0 := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const a
  have diff : HasDerivAt (fun t : ℝ => exp (t*(-1/2))-exp (t*(1/2))) (-1) 0 :=
    ((lin (-1/2)).exp.sub (lin (1/2)).exp).congr_deriv (by norm_num)
  simpa only [zero_add,zero_mul,exp_zero,sub_self,sub_zero,smul_eq_mul,div_eq_inv_mul] using
    diff.tendsto_slope_zero

theorem shell_leading (n : ℕ) :
    Tendsto (fun t => oddTrace (centered (levels (shells (n+1)))) t/t^(2*n+3))
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := ((multiplier_limit 1).pow (n+1)).mul seed_limit
  have expo : 2*n+3=2*(n+1)+1 := by omega
  have den (t : ℝ) : (t^2)^(n+1)*t=t^(2*n+3) := by rw [←pow_mul,expo,pow_succ t (2*(n+1))]
  simpa only [Pi.mul_def,Pi.pow_apply,shell_trace,div_pow,div_mul_div_comm,den,one_pow,one_mul] using h

private theorem ties (n : ℕ) (t : ℝ) :
    oddTrace (centered (levels (shells (n+1)))) t=0 ↔ t=0 := by
  constructor
  · intro hz
    by_contra ht
    rw [shell_trace] at hz
    have zero := (mul_eq_zero.mp hz).resolve_left (pow_pos (multiplier_pos ht one_ne_zero) _).ne'
    have eq := exp_injective (sub_eq_zero.mp zero)
    apply ht
    linarith only [eq]
  · rintro rfl; exact odd_zero _

/-- The very same prime tests the isometry line at every prescribed odd
contact order, and has no extraneous real ties. -/
theorem prime_shell_isometry (n : ℕ) (q : Nat.Primes) (s : ℂ) :
    lawDefect (finiteGibbsStateWeight (2*s.re-1) (primeModes q (shells (n+1)))) 1=0 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [gibbs_defect,one_mul,ties,mul_eq_zero,or_iff_left (log_pos_prime q).ne',split_isometric_iff]
  constructor <;> intro h <;> linarith only [h]

/-- With physical energy restored, the leading coefficient scales as the
same odd power of the elementary energy log q. -/
theorem prime_shell_leading (n : ℕ) (q : Nat.Primes) :
    Tendsto (fun d => lawDefect (finiteGibbsStateWeight d (primeModes q (shells (n+1)))) 1/d^(2*n+3))
      (𝓝[≠] 0) (𝓝 (-(log q.val)^(2*n+3))) := by
  let L := log q.val
  have pos : 0<L := log_pos_prime q
  have damp : Tendsto (fun d : ℝ => d*L) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa only [id_eq,zero_mul] using
        ((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (α := ℝ) (x := 𝓝 0))).mul_const L)
    · filter_upwards [show ∀ᶠ d : ℝ in 𝓝[≠] 0, d≠0 from self_mem_nhdsWithin] with d hd
      exact mul_ne_zero hd pos.ne'
  have lim := ((shell_leading n).comp damp).mul_const (L^(2*n+3))
  rw [neg_one_mul] at lim
  apply lim.congr' (Eventually.of_forall fun d => ?_)
  rw [gibbs_defect,one_mul]
  change _ / (d*L)^(2*n+3)*L^(2*n+3)=_ / d^(2*n+3)
  rw [mul_pow,←div_div]
  exact div_mul_cancel₀ _ (pow_ne_zero _ pos.ne')

#print axioms shell_bound
#print axioms shell_size
#print axioms shell_trace
#print axioms shell_leading
#print axioms prime_shell_isometry
#print axioms prime_shell_leading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder
