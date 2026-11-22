import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityOccupationCubes
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates
import GaloisForLFunctions.HTGeometry.LatticeL2Shift
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge

/-!
# The parity pairing operator

Swapping paired labels and killing singleton cubes gives a bounded odd
self-adjoint operator. Its kernel is the square-shell gas with doubled energy.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.HTGeometry ContinuousLinearMap
open scoped Classical

private def partnerEquiv : (ℕ+ × ℕ+) ≃ (ℕ+ × ℕ+) :=
  ⟨parityPartner, parityPartner, parityPartner_involutive, parityPartner_involutive⟩

private theorem partner_square (x : ℕ+ × ℕ+) :
    parityPartner x ∈ Set.range squareState ↔ x ∈ Set.range squareState := by
  rw [← parityPartner_fixed_iff, ← parityPartner_fixed_iff, parityPartner_involutive x, eq_comm]

/-- The parity pairing exchanges amplitudes along matched edges and vanishes on square states. -/
def parityPairing : PairGas →L[ℂ] PairGas :=
  lpCoordinateProjection (Set.range squareState)ᶜ ∘L
    (lpDomCongr (p := 2) (by norm_num) partnerEquiv).toContinuousLinearEquiv.toContinuousLinearMap

theorem parityPairing_apply (f : PairGas) (x : ℕ+ × ℕ+) :
    parityPairing f x = if x ∈ Set.range squareState then 0 else f (parityPartner x) := by
  rw [parityPairing, comp_apply, lpCoordinateProjection_apply]
  by_cases h : x ∈ Set.range squareState <;> simp [h, Set.indicator, partnerEquiv]

theorem parityPairing_selfAdjoint : parityPairing.adjoint = parityPairing := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine (partnerEquiv.tsum_eq (fun x => inner ℂ (parityPairing f x) (g x))).symm.trans ?_
  apply tsum_congr
  intro x
  change inner ℂ (parityPairing f (parityPartner x)) (g (parityPartner x)) =
    inner ℂ (f x) (parityPairing g x)
  by_cases h : x ∈ Set.range squareState
  · simp only [parityPairing_apply, if_pos ((partner_square x).mpr h), if_pos h, inner_zero_left, inner_zero_right]
  · simp only [parityPairing_apply, if_neg (mt (partner_square x).mp h), if_neg h, parityPartner_involutive x]

/-- Squaring the pairing gives the orthogonal projection onto all paired coordinates. -/
theorem parityPairing_square :
    parityPairing ∘L parityPairing = lpCoordinateProjection (Set.range squareState)ᶜ := by
  ext f x
  change parityPairing (parityPairing f) x = _
  rw [parityPairing_apply, lpCoordinateProjection_apply]
  by_cases h : x ∈ Set.range squareState
  · rw [if_pos h, Set.indicator_of_notMem (show x ∉ (Set.range squareState)ᶜ from fun hc => hc h)]
  · rw [if_neg h, parityPairing_apply, if_neg (mt (partner_square x).mp h), parityPartner_involutive x,
      Set.indicator_of_mem (show x ∈ (Set.range squareState)ᶜ from h)]

/-- Second-copy parity as a bounded observable. -/
def secondParity : PairGas →L[ℂ] PairGas :=
  lpDiagonalCLM (fun x : ℕ+ × ℕ+ => (primeParity x.2 : ℂ)) zero_le_one (fun x => (Circle.norm_coe (primeParity x.2)).le)

theorem parityPairing_anticommutes :
    parityPairing ∘L secondParity = -(secondParity ∘L parityPairing) := by
  ext f x
  change parityPairing (secondParity f) x = -(secondParity (parityPairing f) x)
  by_cases h : x ∈ Set.range squareState
  · simp only [parityPairing_apply, if_pos h, secondParity, lpDiagonalCLM_apply, mul_zero, neg_zero]
  · have hs := parityPartner_sign x (mt (parityPartner_fixed_iff x).mp h)
    simp only [parityPairing_apply, if_neg h, secondParity, lpDiagonalCLM_apply, hs, Circle.coe_neg, neg_mul]

/-- Every bounded function of the total shell label commutes with the pairing. -/
theorem parityPairing_commutes_shell (m : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) :
    let D := lpDiagonalCLM (fun x : ℕ+ × ℕ+ => m (x.1*x.2)) hC (fun x => hm (x.1*x.2))
    parityPairing ∘L D = D ∘L parityPairing := by
  intro D
  ext f x
  change parityPairing (D f) x = m (x.1*x.2) * parityPairing f x
  simp only [parityPairing_apply, D, lpDiagonalCLM_apply, parityPartner_product]
  split <;> simp

theorem mem_parityPairing_ker (f : PairGas) :
    f ∈ parityPairing.ker ↔ ∀ x ∉ Set.range squareState, f x = 0 := by
  change parityPairing f = 0 ↔ _
  constructor
  · intro hf x hx
    have h := congrArg (fun v : PairGas => v (parityPartner x)) hf
    simpa only [parityPairing_apply, partner_square, if_neg hx, parityPartner_involutive x, lp.coeFn_zero,
      Pi.zero_apply] using h
  · intro hf
    apply lp.ext
    funext x
    by_cases h : x ∈ Set.range squareState
    · simp only [parityPairing_apply, if_pos h, lp.coeFn_zero, Pi.zero_apply]
    · rw [parityPairing_apply, if_neg h]
      exact hf _ (mt (partner_square x).mp h)

/-- Isometric identification of the surviving states by their square root label. -/
def squareEmbedding : Gas →ₗᵢ[ℂ] PairGas := _root_.RHTower.lpScalarInjection squareState squareState_injective

theorem squareEmbedding_range : squareEmbedding.toLinearMap.range = parityPairing.ker := by
  ext f
  rw [mem_parityPairing_ker]
  constructor
  · rintro ⟨g,rfl⟩ x hx
    exact _root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x hx
  · intro hf
    let g : Gas := _root_.RHTower.lpCoordinatePullback (E := ℂ) squareState squareState_injective f
    refine ⟨g, ?_⟩
    apply lp.ext
    funext x
    by_cases hx : x ∈ Set.range squareState
    · obtain ⟨n,rfl⟩ := hx
      exact _root_.RHTower.lpScalarInjection_coordinate _ _ g n
    · exact (_root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x hx).trans (hf x hx).symm

def squareKernelEquiv : Gas ≃ₗᵢ[ℂ] parityPairing.ker :=
  squareEmbedding.equivRange.trans (LinearIsometryEquiv.ofEq _ _ squareEmbedding_range)

theorem squareKernelEquiv_coordinate (f : Gas) (n : ℕ+) :
    (squareKernelEquiv f : PairGas) (squareState n) = f n :=
  _root_.RHTower.lpScalarInjection_coordinate squareState squareState_injective f n

/-- The absolute heat trace on the unpaired basis converges exactly beyond half. -/
theorem squareKernel_summable_iff (s : ℂ) :
    (Summable fun n : ℕ+ => ‖heat s ((squareState n).1 * (squareState n).2)‖) ↔ 1/2 < s.re := by
  change (Summable fun n : ℕ+ => ‖heat s (1*(n*n))‖) ↔ _
  simpa only [one_mul, heat_mul, norm_mul, sq] using summable_heat_sq_iff s

theorem squareKernelEquiv_symm_coordinate (v : parityPairing.ker) (n : ℕ+) :
    squareKernelEquiv.symm v n = (v : PairGas) (squareState n) := by
  have h := squareKernelEquiv_coordinate (squareKernelEquiv.symm v) n
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

/-- Transport an observable to the surviving Hilbert space by labeling each square with its root. -/
def squareKernelTransport (A : Gas →L[ℂ] Gas) : parityPairing.ker →L[ℂ] parityPairing.ker :=
  squareKernelEquiv.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    squareKernelEquiv.symm.toLinearIsometry.toContinuousLinearMap

theorem squareKernelTransport_trace (A : Gas →L[ℂ] Gas) (hA : A.IsTraceClass) :
    opTrace (squareKernelTransport A) = opTrace A :=
  _root_.RHTower.opTrace_unitaryConjugate_of_isTraceClass squareKernelEquiv.symm A hA

private def doubledTemperature (s : {w : ℂ // 1/2 < w.re}) : {w : ℂ // 1 < w.re} :=
  ⟨s.val+s.val, by rw [Complex.add_re]; linarith only [s.property]⟩

private theorem gibbs_traceClass (t : {w : ℂ // 1 < w.re}) : (gibbsOperator t).IsTraceClass :=
  (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

/-- Heat propagation on the kernel, in its actual Hilbert space. -/
def squareKernelHeat (s : {w : ℂ // 1/2 < w.re}) : parityPairing.ker →L[ℂ] parityPairing.ker :=
  squareKernelTransport (gibbsOperator (doubledTemperature s))

theorem squareKernelHeat_apply (s : {w : ℂ // 1/2 < w.re}) (f : parityPairing.ker) (n : ℕ+) :
    (squareKernelHeat s f : PairGas) (squareState n) =
      heat s.val ((squareState n).1*(squareState n).2) * (f : PairGas) (squareState n) := by
  change (squareKernelEquiv (gibbsOperator (doubledTemperature s) (squareKernelEquiv.symm f)) : PairGas) (squareState n) = _
  rw [squareKernelEquiv_coordinate, gibbsOperator_apply, squareKernelEquiv_symm_coordinate]
  change heat (s.val+s.val) n * _ = heat s.val (1*(n*n)) * _
  rw [one_mul, heat_add, heat_mul]

theorem squareKernelHeat_trace (s : {w : ℂ // 1/2 < w.re}) :
    opTrace (squareKernelHeat s) = riemannZeta (2*s.val) := by
  rw [squareKernelHeat, squareKernelTransport_trace _ (gibbs_traceClass _), partition_eq_zeta, two_mul]
  rfl

/-- Every trace-class shell multiplier has absolutely summable weights on the surviving basis. -/
theorem squareKernel_diagonal_summable (T : parityPairing.ker →L[ℂ] parityPairing.ker)
    (hT : T.IsTraceClass) (d : ℕ+ → ℂ)
    (hact : ∀ (f : parityPairing.ker) (n : ℕ+), (T f : PairGas) (squareState n) = d n * (f : PairGas) (squareState n)) :
    Summable (fun n => ‖d n‖) := by
  obtain ⟨A,B,hA,hB,hT⟩ := hT
  let b : HilbertBasis ℕ+ ℂ parityPairing.ker := HilbertBasis.ofRepr squareKernelEquiv.symm
  have hb (n : ℕ+) : squareKernelEquiv.symm (b n) = lp.single 2 n 1 := b.repr_self n
  have hd := (summable_inner_diag_comp hA hB b).norm
  refine hd.congr fun n => congrArg norm ?_
  rw [← hT, ← squareKernelEquiv.symm.inner_map_map, hb, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one, squareKernelEquiv_symm_coordinate, hact]
  rw [← squareKernelEquiv_symm_coordinate, hb, lp.single_apply_self, mul_one]

/-- A trace-class operator on the kernel can have the shell heat action precisely in the open half-plane. -/
theorem squareKernel_traceClass_iff (s : ℂ) :
    (∃ T : parityPairing.ker →L[ℂ] parityPairing.ker, T.IsTraceClass ∧
      ∀ (f : parityPairing.ker) (n : ℕ+), (T f : PairGas) (squareState n) =
        heat s ((squareState n).1*(squareState n).2) * (f : PairGas) (squareState n)) ↔ 1/2 < s.re := by
  constructor
  · rintro ⟨T,hT,hact⟩
    exact (squareKernel_summable_iff s).mp (squareKernel_diagonal_summable T hT _ hact)
  · intro hs
    let t := doubledTemperature ⟨s,hs⟩
    exact ⟨squareKernelHeat ⟨s,hs⟩, _root_.RHTower.ccmIsTraceClass_unitaryConjugate
      squareKernelEquiv.symm (gibbsOperator t) (gibbs_traceClass t), squareKernelHeat_apply ⟨s,hs⟩⟩

#print axioms parityPairing_selfAdjoint
#print axioms parityPairing_square
#print axioms parityPairing_anticommutes
#print axioms parityPairing_commutes_shell
#print axioms squareKernelEquiv
#print axioms squareKernel_summable_iff
#print axioms squareKernelHeat_apply
#print axioms squareKernelHeat_trace
#print axioms squareKernel_traceClass_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
