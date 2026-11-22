import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityGradingRigidity

/-!
# The quarter-turn insertion

A quarter-turn per prime makes the square-shell trace vanish to first order
at its trace-class boundary. Its meromorphic continuation has a pole at one quarter.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open ContinuousLinearMap GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroForcingCalculus

private def doubleParameter (s : {w : ℂ // 1/2 < w.re}) : {w : ℂ // 1 < w.re} :=
  ⟨2*s.val, by rw [two_mul,Complex.add_re]; linarith only [s.property]⟩

private def insertedHeat (u : ℕ+ → Circle) (z : {w : ℂ // 1 < w.re}) :=
  thermalPhaseOperator ⟨z.val.re,z.property⟩ (fun n => u n / clockPhase z.val.im n)

private theorem insertedHeat_tc (u : ℕ+ → Circle) (z : {w : ℂ // 1 < w.re}) :
    (insertedHeat u z).IsTraceClass :=
  (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

private theorem insertedHeat_apply (u : ℕ+ → Circle) (z : {w : ℂ // 1 < w.re}) (f : Gas) (n : ℕ+) :
    insertedHeat u z f n = (u n : ℂ) * heat z.val n * f n := by
  rw [insertedHeat, thermalPhaseOperator_apply, Circle.coe_div, div_eq_mul_inv, mul_assoc (u n : ℂ)]
  congr 2
  change (Complex.exp (((z.val.im*energy n : ℝ) : ℂ)*Complex.I))⁻¹ *
    (Real.exp (-z.val.re * energy n) : ℂ) = heat z.val n
  rw [← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add, heat,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  calc
    _ = -((z.val.re : ℂ)+(z.val.im : ℂ)*Complex.I)*(energy n : ℂ) := by ring
    _ = _ := by rw [Complex.re_add_im]

/-- Complex-temperature heat operator with the common two-copy phase on the kernel. -/
def squareInsertedHeat (χ : ℕ+ →* Circle) (s : {w : ℂ // 1/2 < w.re}) :=
  squareKernelTransport (insertedHeat (χ^2 : ℕ+ →* Circle) (doubleParameter s))

theorem squareInsertedHeat_apply (χ : ℕ+ →* Circle) (s : {w : ℂ // 1/2 < w.re})
    (f : parityPairing.ker) (n : ℕ+) :
    (squareInsertedHeat χ s f : PairGas) (squareState n) =
      ((χ n : ℂ)^2 * heat s.val ((squareState n).1*(squareState n).2)) * (f : PairGas) (squareState n) := by
  change (squareKernelEquiv (insertedHeat _ _ (squareKernelEquiv.symm f)) : PairGas) (squareState n) = _
  rw [squareKernelEquiv_coordinate, insertedHeat_apply, squareKernelEquiv_symm_coordinate]
  change (((χ n)^2 : Circle) : ℂ) * heat (2*s.val) n * _ = _ * heat s.val (1*(n*n)) * _
  rw [Circle.coe_pow, two_mul, one_mul, heat_add, heat_mul]

/-- Existence of a trace-class realization of the phase-weighted shell dynamics. -/
def HasSquarePhaseHeat (χ : ℕ+ →* Circle) (s : ℂ) : Prop :=
  ∃ T : parityPairing.ker →L[ℂ] parityPairing.ker, T.IsTraceClass ∧
    ∀ (f : parityPairing.ker) (n : ℕ+), (T f : PairGas) (squareState n) =
      ((χ n : ℂ)^2 * heat s ((squareState n).1*(squareState n).2)) * (f : PairGas) (squareState n)

/-- No choice of unitary prime phases moves the trace-class boundary. -/
theorem squareInserted_traceClass_iff (χ : ℕ+ →* Circle) (s : ℂ) :
    HasSquarePhaseHeat χ s ↔ 1/2 < s.re := by
  constructor
  · rintro ⟨T,hT,hact⟩
    exact (squarePhase_summable_iff χ s).mp (squareKernel_diagonal_summable T hT _ hact)
  · intro hs
    exact ⟨squareInsertedHeat χ ⟨s,hs⟩, _root_.RHTower.ccmIsTraceClass_unitaryConjugate
      squareKernelEquiv.symm _ (insertedHeat_tc _ _), squareInsertedHeat_apply χ ⟨s,hs⟩⟩

/-- The order split is isometric precisely at the trace-class boundary of the graded kernel. -/
theorem split_isometry_iff_kernel_heat_boundary (χ : ℕ+ →* Circle) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ¬HasSquarePhaseHeat χ s ∧ ∀ δ : ℝ, 0 < δ → HasSquarePhaseHeat χ (s+(δ : ℂ)) := by
  rw [split_isometric_iff]
  simp only [squareInserted_traceClass_iff, not_lt, Complex.add_re, Complex.ofReal_re]
  constructor
  · intro h
    exact ⟨h.le,fun δ hδ => by linarith only [h,hδ]⟩
  · rintro ⟨hs,hr⟩
    apply le_antisymm hs
    by_contra! h
    have h' := hr (1/2-s.re) (sub_pos.mpr h)
    linarith only [h']

private def quarterTurn : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩

/-- A quarter-turn for each prime quantum, extended to every occupation. -/
def quarterPhase : ℕ+ →* Circle :=
  (prime_phase_coordinates.surjective (fun _ => quarterTurn)).choose

private theorem quarterPhase_prime (p : Nat.Primes) : quarterPhase (p : ℕ+) = quarterTurn :=
  congrFun (prime_phase_coordinates.surjective (fun _ => quarterTurn)).choose_spec p

theorem quarterPhase_square : quarterPhase^2 = primeParity := by
  apply prime_phase_coordinates.injective
  funext p
  change (quarterPhase (p : ℕ+))^2 = primeParity (p : ℕ+)
  rw [quarterPhase_prime, primeParity_prime]
  apply Circle.coe_injective
  change Complex.I^2 = -1
  exact Complex.I_sq

/-- The continued kernel trace for a quarter-turn per prime. -/
def quarterPartition (s : ℂ) := parityPartition (2*s)

theorem quarterPartition_trace (s : {w : ℂ // 1/2 < w.re}) :
    opTrace (squareInsertedHeat quarterPhase s) = quarterPartition s.val := by
  rw [squareInsertedHeat, quarterPhase_square, squareKernelTransport_trace _ (insertedHeat_tc _ _)]
  exact parity_trace (doubleParameter s)

private theorem quarterPartition_quotient :
    quarterPartition = (fun w : ℂ => riemannZeta (4*w)) / (fun w : ℂ => riemannZeta (2*w)) := by
  funext w
  change riemannZeta (2*(2*w)) / _ = riemannZeta (4*w) / _
  rw [show 2*(2*w) = 4*w by ring]

theorem quarterPartition_meromorphic (s : ℂ) : MeromorphicAt quarterPartition s := by
  rw [quarterPartition_quotient]
  exact (meromorphicOrderAt_riemannZeta_const_mul (c := 4) (by norm_num) s).1.div
    (meromorphicOrderAt_riemannZeta_const_mul two_ne_zero s).1

theorem quarterPartition_order (s : ℂ) :
    meromorphicOrderAt quarterPartition s = meromorphicOrderAt parityPartition (2*s) := by
  have h₂ := meromorphicOrderAt_riemannZeta_const_mul (c := 2) two_ne_zero s
  have h₄ := meromorphicOrderAt_riemannZeta_const_mul (c := 4) (by norm_num) s
  rw [quarterPartition_quotient, meromorphicOrderAt_div h₄.1 h₂.1, h₄.2, h₂.2, parityPartition_order,
    show 2*(2*s) = 4*s by ring]

theorem quarterPartition_positive_order (x : {r : ℝ // 0 < r}) :
    meromorphicOrderAt quarterPartition (x.val : ℂ) =
      if x.val=1/4 then -1 else if x.val=1/2 then 1 else 0 := by
  have hp : 2*x.val=1/2 ↔ x.val=1/4 := by constructor <;> intro h <;> linarith only [h]
  have hz : 2*x.val=1 ↔ x.val=1/2 := by constructor <;> intro h <;> linarith only [h]
  have hc : 2*(x.val : ℂ) = ((2*x.val : ℝ) : ℂ) := by push_cast; rfl
  rw [quarterPartition_order, hc, parityPartition_positive_order ⟨2*x.val,mul_pos zero_lt_two x.property⟩]
  simp only [hp,hz]

#print axioms squareInsertedHeat_apply
#print axioms squareInserted_traceClass_iff
#print axioms split_isometry_iff_kernel_heat_boundary
#print axioms quarterPhase_square
#print axioms quarterPartition_trace
#print axioms quarterPartition_meromorphic
#print axioms quarterPartition_order
#print axioms quarterPartition_positive_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
