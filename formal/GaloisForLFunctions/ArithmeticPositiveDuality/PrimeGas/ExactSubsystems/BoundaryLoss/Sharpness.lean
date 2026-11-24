import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Boxes
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.PrimeRay

/-! # The Euler visibility is the exact infimum over finite independent factors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

private def heatHom (s : ℂ) : ℕ+ →* ℂ where
  toFun := heat s
  map_one' := by simp [heat,energy]
  map_mul' := heat_mul s

theorem box_trace (P : Finset Nat.Primes) (d : ℕ+) (s : ℂ) :
    finiteHeatTrace (boxLabel P d) s = ∏ p ∈ P, ∑ j : Fin d.val, (heat s (primePNat p))^j.val := by
  classical
  change (∑ i : BoxDigits P d, heatHom s (boxLabel P d i)) = _
  simp only [boxLabel_product,map_prod,map_pow]
  exact (Fintype.prod_sum (fun (p : P) (j : Fin d.val) => (heat s (primePNat p.val))^j.val)).symm.trans
    (Finset.prod_coe_sort P (fun p => ∑ j : Fin d.val, (heat s (primePNat p))^j.val))

def growingRadix (k : ℕ) : ℕ+ := ⟨k+1,Nat.succ_pos _⟩

theorem box_trace_limit (P : Finset Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun k => finiteHeatTrace (boxLabel P (growingRadix k)) s) atTop
      (𝓝 (RHTower.thetaEulerStageZeta (primeWindow P) s)) := by
  have hp (p : Nat.Primes) : Tendsto (fun k : ℕ => ∑ j : Fin (k+1), (heat s (primePNat p))^j.val) atTop
      (𝓝 ((1-heat s (primePNat p))⁻¹)) := by
    simp_rw [Fin.sum_univ_eq_sum_range]
    exact (hasSum_geometric_of_norm_lt_one (prime_heat_lt_one hs p)).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have he : RHTower.thetaEulerStageZeta (primeWindow P) s = ∏ p ∈ P, (1-heat s (primePNat p))⁻¹ := by
    simp only [RHTower.thetaEulerStageZeta,primeWindow,Finset.prod_map,heat_eq_cpow]
    rfl
  rw [he]
  simp only [box_trace]
  exact tendsto_finsetProd P (fun p _ => hp p)

theorem box_visibility_limit (P : Finset Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun k => traceVisibility (boxLabel P (growingRadix k)) s) atTop (𝓝 (eulerEnvelope P s)) := by
  rw [euler_normalization]
  exact (box_trace_limit P hs).norm.div (box_trace_limit P (s := (s.re:ℂ)) hs).norm
    (norm_ne_zero_iff.mpr (RHTower.thetaEulerStageZeta_ne_zero _ (primeWindow_primes P) hs))

/-- The observable visibilities, represented by the finite set of distinct physical labels. -/
def attainedVisibilities (P : Finset Nat.Primes) (s : ℂ) : Set ℝ := {v |
  ∃ (A : Finset ℕ+) (B : Set ℕ+),
    exactLabelProduct (fun i : A => i.val) (fun j : B => j.val) ∧
    (∀ i : A, i.val.val ∈ Nat.factoredNumbers (primeWindow P)) ∧
    v = traceVisibility (fun i : A => i.val) s}

/-- Renaming the states leaves the physical visibility unchanged. -/
theorem visibility_mem {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P)) (s : ℂ) :
    traceVisibility a s ∈ attainedVisibilities P s := by
  classical
  obtain ⟨v,_⟩ := h.2 1
  have hi : Function.Injective a := fun i j he =>
    congrArg Prod.fst (h.1 (a₁ := (i,v.2)) (a₂ := (j,v.2)) (congrArg (· * b v.2) he))
  let A := Finset.univ.image a
  let f (i : ι) : A := ⟨a i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let e : ι ≃ A := Equiv.ofBijective f ⟨fun _ _ he => hi (congrArg Subtype.val he),fun i => by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp i.property
    exact ⟨j,Subtype.ext hj⟩⟩
  have he (z : ℂ) : finiteHeatTrace a z = finiteHeatTrace (fun i : A => i.val) z :=
    e.sum_comp (fun i => heat z i.val)
  have hb := exact_range_right h
  refine ⟨A,Set.range b,?_,?_,by rw [traceVisibility,traceVisibility,he,he]⟩
  · constructor
    · intro x y hh
      have hv := hb.1 (a₁ := (e.symm x.1,x.2)) (a₂ := (e.symm y.1,y.2)) (by
        have hx : a (e.symm x.1) = x.1.val := congrArg Subtype.val (e.apply_symm_apply x.1)
        have hy : a (e.symm y.1) = y.1.val := congrArg Subtype.val (e.apply_symm_apply y.1)
        change a (e.symm x.1)*x.2.val = a (e.symm y.1)*y.2.val
        rw [hx,hy]
        exact hh)
      have h₂ := congrArg (fun u : ι × Set.range b => u.2) hv
      exact Prod.ext (e.symm.injective (congrArg Prod.fst hv)) h₂
    · intro n
      obtain ⟨⟨i,j⟩,hn⟩ := hb.2 n
      exact ⟨(e i,j),hn⟩
  · intro i
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp i.property
    rw [← hj]
    exact ha j

/-- The bound is sharp at each complex temperature, even when only finite factors are allowed. -/
theorem visibility_isGLB (P : Finset Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    IsGLB (attainedVisibilities P s) (eulerEnvelope P s) := by
  constructor
  · rintro _ ⟨A,B,h,ha,rfl⟩
    exact envelope_le_visibility P h ha hs
  · intro c hc
    exact ge_of_tendsto (box_visibility_limit P hs) (Eventually.of_forall (fun k =>
      hc (visibility_mem P (box_exact P (growingRadix k)) (box_supported P (growingRadix k)) s)))

#print axioms box_trace
#print axioms box_trace_limit
#print axioms box_visibility_limit
#print axioms visibility_mem
#print axioms visibility_isGLB

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
