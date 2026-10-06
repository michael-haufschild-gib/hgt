import GaloisForLFunctions.RHTower.ChiCubicSchwartzPoisson
import GaloisForLFunctions.RHTower.ChiCubicExteriorRapidDecay
import GaloisForLFunctions.RHTower.ChiRamanujanCriticalSourceControl
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicDefectAction

/-!
# Complete projected arithmetic exterior

Full Schwartz Poisson identifies every lifted physical test with its
periodic lattice series. One fixed finite Schwartz seminorm controls
the entire projected critical source, uniformly in its prime set and
modulus. The actual shrinking exterior therefore has arbitrary power
decay with every atom, lift, alias and both projectors retained.
-/

noncomputable section
open Set Filter
open scoped Topology FourierTransform
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace
private abbrev X := ℝ × ℝ × ℝ
private def coords (x : X) : E := WithLp.toLp 2 ![x.1,x.2.1,x.2.2]

private theorem coords_growth : coords.HasTemperateGrowth := by
  let e (i : Fin 3) : E := EuclideanSpace.single i 1
  have he : coords = fun x : X => x.1 • e 0+x.2.1 • e 1+x.2.2 • e 2 := by
    funext x
    ext i
    fin_cases i <;> simp [coords,e]
  have h0 : (fun x : X => x.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasTemperateGrowth
  have h1 : (fun x : X => x.2.1).HasTemperateGrowth :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasTemperateGrowth
  have h2 : (fun x : X => x.2.2).HasTemperateGrowth :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasTemperateGrowth
  rw [he]
  fun_prop

private theorem coords_lower (x : X) : ‖x‖ ≤ 1+‖coords x‖ := by
  have h0 : ‖x.1‖ ≤ ‖coords x‖ := PiLp.norm_apply_le (coords x) 0
  have h1 : ‖x.2.1‖ ≤ ‖coords x‖ := PiLp.norm_apply_le (coords x) 1
  have h2 : ‖x.2.2‖ ≤ ‖coords x‖ := PiLp.norm_apply_le (coords x) 2
  have hn : ‖x‖ ≤ ‖coords x‖ := by
    rw [Prod.norm_def,Prod.norm_def]
    exact max_le h0 (max_le h1 h2)
  linarith

/-- Exact product coordinates for the original physical Schwartz test. -/
def bagPhysicalProductSchwartz : SchwartzMap E ℂ →L[ℂ] SchwartzMap X ℂ :=
  SchwartzMap.compCLM ℂ coords_growth ⟨1,1,by simpa using coords_lower⟩

private theorem product_apply (f : SchwartzMap E ℂ) (x : X) :
    bagPhysicalProductSchwartz f x=f (coords x) := rfl

private theorem phase (n : ℤ × ℤ × ℤ) (x : X) :
    Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) (coords x) : ℝ)*Complex.I) =
      ramanujanTripleFourierPhase n x := by
  simp only [bagIntegerTriple,coords,PiLp.inner_apply,Real.inner_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,ramanujanTripleFourierPhase,ramanujanFourierPhase]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every lifted Fourier frequency of ANY physical Schwartz function
matches its complete periodic physical test. No compact support premise. -/
theorem bagLiftedFourierTest_eq_periodic (f : SchwartzMap E ℂ) :
    bagLiftedFourierTest f = ramanujanTriplePeriodicTest (bagPhysicalProductSchwartz f) := by
  funext x
  change (∑' k : ℤ × ℤ × ℤ, (𝓕 f) (bagIntegerTriple k-coords x)) = _
  rw [FullPoisson.full_schwartz_poisson]
  unfold ramanujanTriplePeriodicTest
  apply tsum_congr
  intro n
  rw [phase,product_apply]
  have hc : coords (ramanujanTripleLattice n)=bagIntegerTriple n := rfl
  rw [hc,mul_comm]

private theorem product_seminorm_control :
    ∃ K : Finset (ℕ × ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ f : SchwartzMap E ℂ,
      ramanujanTripleSeminorm (bagPhysicalProductSchwartz f) ≤
        B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
  have hp : Continuous (ramanujanTripleSeminorm : SchwartzMap X ℂ → ℝ) := by
    apply Seminorm.continuous_finsetSup
    intro i hi
    exact (schwartz_withSeminorms ℂ X ℂ).continuous_seminorm i
  let q : Seminorm ℂ (SchwartzMap E ℂ) :=
    ramanujanTripleSeminorm.comp bagPhysicalProductSchwartz.toLinearMap
  have hq : Continuous q := hp.comp bagPhysicalProductSchwartz.continuous
  obtain ⟨K,B,_,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  refine ⟨K,B,B.coe_nonneg,fun f => ?_⟩
  have he := hb f
  rw [_root_.smul_apply,NNReal.smul_def,smul_eq_mul] at he
  exact he

/-- One fixed physical Schwartz seminorm family controls the COMPLETE
critical atom action, ALL lifts and BOTH projectors, uniformly in EVERY
prime-source set and projector modulus. No atom absolute-mass loss. -/
theorem bagCriticalDefectAction_uniform_seminorm :
    ∃ K : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset ℕ, ∀ D : ℕ+, ∀ f : SchwartzMap E ℂ,
        ‖bagCriticalDefectAction P D f‖ ≤ C*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
  obtain ⟨A,hA,hAb⟩ := ramanujanTripleSchwartz_weighted_sum_le
  obtain ⟨K,B,hB,hBb⟩ := product_seminorm_control
  refine ⟨K,A*B+1,by positivity,fun P D f => ?_⟩
  rw [bagCriticalDefectAction_eq,bagLiftedFourierTest_eq_periodic]
  calc
    _ ≤ ∑' n : ℤ × ℤ × ℤ, ‖bagPhysicalProductSchwartz f (ramanujanTripleLattice n)‖*
        ramanujanTripleWeight (ramanujanTripleLattice n) :=
      ramanujanCriticalTripleAtomAction_projected_periodic_bound P D (bagPhysicalProductSchwartz f)
    _ ≤ A*ramanujanTripleSeminorm (bagPhysicalProductSchwartz f) := hAb _
    _ ≤ A*(B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f) :=
      mul_le_mul_of_nonneg_left (hBb f) hA.le
    _ ≤ (A*B+1)*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)

/-- The COMPLETE projected arithmetic exterior of the original moving
amplitude has arbitrary polynomial decay. The constant is independent
of the entire prime set P and projector modulus D; all rational atoms,
integer lifts, aliases and both contraction exclusions are retained. -/
theorem bagCubicShrinkingExterior_source_rapid_decay (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : BAGCubicExteriorScale, ∀ P : Finset ℕ, ∀ D : ℕ+,
      ‖bagCriticalDefectAction P D (bagCubicShrinkingExterior N)‖ ≤ C/N.1^a := by
  obtain ⟨K,B,hB,hBb⟩ := bagCriticalDefectAction_uniform_seminorm
  choose A hA hAb using fun i : ℕ × ℕ => bagCubicShrinkingExterior_rapid_decay i.1 i.2 a
  let C : ℝ := 1+∑ i ∈ K, A i
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i ∈ K, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp only [C]; linarith
  refine ⟨B*C,mul_pos hB hC,fun N P D => ?_⟩
  have hN : 0 < N.1 := lt_of_lt_of_le (Real.exp_pos 1) N.2.1
  have hs : (K.sup (schwartzSeminormFamily ℂ E ℂ)) (bagCubicShrinkingExterior N) ≤ C/N.1^a := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hAC : A i ≤ C := (Finset.single_le_sum (fun j _ => (hA j).le) hi).trans
      (by dsimp only [C]; linarith)
    exact (hAb i N).trans (div_le_div_of_nonneg_right hAC (pow_nonneg hN.le a))
  calc
    _ ≤ B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) (bagCubicShrinkingExterior N) := hBb P D _
    _ ≤ B*(C/N.1^a) := mul_le_mul_of_nonneg_left hs hB.le
    _ = _ := by ring

end RHTower.BAGTrace
