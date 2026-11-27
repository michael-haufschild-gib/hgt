import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Implication

/-! # Integer substitutions in shell evaluation kernels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real MvPolynomial

private theorem powers (s : ℝ) (m : ℕ) : coordinates (s*m)=(coordinates s)^m := by
  funext p
  exact rpow_mul_natCast (by positivity : 0 ≤ (p.val : ℝ)) s m

theorem kernel_dilate {s u : ℝ} (h : kernel s ≤ kernel u) (m : ℕ) :
    kernel (s*m) ≤ kernel (u*m) := by
  intro P hp
  have eq (v : ℝ) : value v (expand m P)=value (v*m) P := by rw [value,aeval_expand,← powers]; rfl
  exact (eq u).symm.trans (show value u (expand m P)=0 from h ((eq s).trans hp))

/-- Multiplying every reciprocal shell by the product of all occupied labels
clears the denominators in a polynomial at negative order. -/
theorem reciprocal_certificate (P : PolynomialRing) :
    ∃ (Q : PolynomialRing) (d : ℕ+), ∀ s, value s Q=exp (s*energy d)*value (-s) P := by
  classical
  let S := P.support
  let d := ∏ v ∈ S, label v
  let b (v : Exponent) := ∏ w ∈ S.erase v, label w
  let Q := ∑ v ∈ S, C (coeff v P)*atom (b v)
  refine ⟨Q,d,fun s => ?_⟩
  rw [value_sum P]
  simp only [Q,map_sum,map_mul,value_atom,mul_sum,shellPower_exp]
  apply sum_congr rfl
  intro v hv
  have de : energy d=energy (b v)+energy (label v) := by
    rw [← energy_mul]
    exact congrArg energy (prod_erase_mul S label hv).symm
  rw [value,aeval_C]
  change ((coeff v P : ℤ) : ℝ)*exp (s*energy (b v))=_
  rw [mul_left_comm (exp _),← exp_add,de]
  congr 2
  ring

theorem kernel_negate {s u : ℝ} (h : kernel s ≤ kernel u) : kernel (-s) ≤ kernel (-u) := by
  intro P hp
  obtain ⟨Q,d,eq⟩ := reciprocal_certificate P
  have root : Q ∈ kernel s := by
    change value s Q=0
    rw [eq,show value (-s) P=0 from hp,mul_zero]
  have dst : value u Q=0 := h root
  rw [eq,mul_eq_zero] at dst
  exact dst.resolve_left (exp_pos _).ne'

/-- Squaring a rational dilation removes the sign ambiguity of a forced reading. -/
theorem squared_step {t u : ℝ} (ht : 0<t) (hu : 0<u) (h : Forces t u)
    (a b : ℕ) (eq : u*b=t*a) : kernel (t*(b^2 : ℕ)) ≤ kernel (t*(a^2 : ℕ)) := by
  rcases (forces_iff ht hu).mp h with pos | neg
  · have left := kernel_dilate pos (b*b)
    have right := kernel_dilate pos (a*b)
    have mid : u*(↑(b*b) : ℝ)=t*↑(a*b) := by push_cast; linear_combination (b : ℝ)*eq
    have last : u*(↑(a*b) : ℝ)=t*(a^2 : ℕ) := by push_cast; linear_combination (a : ℝ)*eq
    rw [mid] at left
    rw [last] at right
    simpa only [sq] using left.trans right
  · have left := kernel_dilate neg (b*b)
    have right := kernel_dilate (kernel_negate neg) (a*b)
    have mid : -u*(↑(b*b) : ℝ)= -t*↑(a*b) := by push_cast; linear_combination -(b : ℝ)*eq
    have last : u*(↑(a*b) : ℝ)=t*(a^2 : ℕ) := by push_cast; linear_combination (a : ℝ)*eq
    rw [mid] at left
    rw [neg_neg,last] at right
    simpa only [sq] using left.trans right

variable {ι : Type*}

def sample (a : ι → ℕ+) (s : ℝ) : MvPolynomial ι ℤ →ₐ[ℤ] ℝ :=
  aeval (fun i => exp (s*energy (a i)))

def sampledKernel (a : ι → ℕ+) (s : ℝ) := RingHom.ker (sample a s).toRingHom

theorem restrict_kernel (a : ι → ℕ+) {s u : ℝ} (h : kernel s ≤ kernel u) :
    sampledKernel a s ≤ sampledKernel a u := by
  let sub := (aeval (fun i => atom (a i)) : MvPolynomial ι ℤ →ₐ[ℤ] PolynomialRing)
  have eq (v : ℝ) : (value v).comp sub=sample a v := by
    ext i
    simp only [AlgHom.comp_apply,sub,sample,aeval_X,value_atom]
  intro P hp
  change sample a u P=0
  rw [← eq u]
  apply h (x := sub P)
  change (value s).comp sub P=0
  rw [eq]
  exact hp

#print axioms reciprocal_certificate
#print axioms squared_step
#print axioms restrict_kernel

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
