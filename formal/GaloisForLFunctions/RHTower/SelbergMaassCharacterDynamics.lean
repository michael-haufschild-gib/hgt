import GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux

/-!
# Original character dynamics and physical side matching

Every fixed continuous linear observation of the original Maass source retains
both real coordinate derivatives and the same scalar eigen-potential. The full
mass Laplacian of each actual character projection therefore retains its complete
physical gradient. Complete block commutation and original derivative transport
prove unit translation symmetry and matching physical side currents.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassCongruenceAverage SelbergMaassCharacterGradient
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassCharacterSeamFlux SelbergMaassMean
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- A fixed observation retains the complete original physical derivative. -/
theorem source_readout_dir (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (v : ℂ) (z : ℍ) :
    dir v (fun w => L (sourceVector N f (ofComplex w))) (z : ℂ) =
      L (dir v (fun w => sourceVector N f (ofComplex w)) (z : ℂ)) := by
  have hf := (sourceVector_contDiffOn N f).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have h := (L.restrictScalars ℝ).hasFDerivAt.comp (z : ℂ)
    (hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  exact congrArg (fun M => M v) h.fderiv

/-- Both actual real derivatives commute with a fixed observation of the source. -/
theorem source_readout_second_dir (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (v : ℂ) (z : ℍ) :
    dir v (dir v (fun w => L (sourceVector N f (ofComplex w)))) (z : ℂ) =
      L (dir v (dir v (fun w => sourceVector N f (ofComplex w))) (z : ℂ)) := by
  have hf := (sourceVector_contDiffOn N f).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have he : dir v (fun w => L (sourceVector N f (ofComplex w))) =ᶠ[𝓝 (z : ℂ)]
      (fun w => L (dir v (fun u => sourceVector N f (ofComplex u)) w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have h := source_readout_dir N f L v (ofComplex w)
    simpa only [ofComplex_apply_of_im_pos hw] using h
  have h := (L.restrictScalars ℝ).hasFDerivAt.comp (z : ℂ)
    ((dir_contDiffAt hf v).differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  change fderiv ℝ _ (z : ℂ) v = _
  rw [he.fderiv_eq]
  exact congrArg (fun M => M v) h.fderiv

/-- The complete original vector obeys its actual scalar Maass potential. -/
theorem sourceVector_laplacian (z : ℍ) :
    dir 1 (dir 1 (fun w => sourceVector N f (ofComplex w))) (z : ℂ) +
      dir Complex.I (dir Complex.I (fun w => sourceVector N f (ofComplex w))) (z : ℂ) =
      ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ) • sourceVector N f z := by
  ext q
  have h1 := source_readout_second_dir N f (EuclideanSpace.proj q) 1 z
  have hi := source_readout_second_dir N f (EuclideanSpace.proj q) Complex.I z
  change dir 1 (dir 1 (field N f q)) (z : ℂ) =
    (dir 1 (dir 1 (fun w => sourceVector N f (ofComplex w))) (z : ℂ)) q at h1
  change dir Complex.I (dir Complex.I (field N f q)) (z : ℂ) =
    (dir Complex.I (dir Complex.I (fun w => sourceVector N f (ofComplex w))) (z : ℂ)) q at hi
  change (dir 1 (dir 1 (fun w => sourceVector N f (ofComplex w))) (z : ℂ)) q +
    (dir Complex.I (dir Complex.I (fun w => sourceVector N f (ofComplex w))) (z : ℂ)) q =
    ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*sourceVector N f z q
  rw [← h1,← hi]
  change _ = ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*(quotientForm N f q).1.1 z
  simpa only [field,Function.comp_apply,ofComplex_apply] using field_laplacian N f q z

/-- Every fixed observation retains the original Maass equation, even when it vanishes. -/
theorem source_readout_laplacian (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (z : ℍ) :
    dir 1 (dir 1 (fun w => L (sourceVector N f (ofComplex w)))) (z : ℂ) +
      dir Complex.I (dir Complex.I (fun w => L (sourceVector N f (ofComplex w)))) (z : ℂ) =
      ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*L (sourceVector N f z) := by
  rw [source_readout_second_dir,source_readout_second_dir,← map_add,sourceVector_laplacian,map_smul,smul_eq_mul]

/-- Actual projected source components retain C² regularity. -/
theorem characterField_contDiffOn (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) :
    ContDiffOn ℝ 2 (characterField N f p r q) {z : ℂ | 0 < z.im} :=
  readout_contDiffOn N f ((EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap)

/-- Actual projected components obey the original equation with its full height factor. -/
theorem characterField_laplacian (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) (z : ℍ) :
    dir 1 (dir 1 (characterField N f p r q)) (z : ℂ) +
      dir Complex.I (dir Complex.I (characterField N f p r q)) (z : ℂ) =
      ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*characterField N f p r q (z : ℂ) := by
  have h := source_readout_laplacian N f
    ((EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap) z
  change dir 1 (dir 1 (characterField N f p r q)) (z : ℂ) +
    dir Complex.I (dir Complex.I (characterField N f p r q)) (z : ℂ) =
      ((-(lam/z.im^(2 : ℕ)) : ℝ) : ℂ)*(characterProjection N p r (sourceVector N f z)) q at h
  simpa only [characterField,ofComplex_apply] using h

/-- The physical derivative of each projected field is the projected original derivative. -/
theorem characterField_dir (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) (v : ℂ) (z : ℍ) :
    dir v (characterField N f p r q) (z : ℂ) =
      characterProjection N p r (sourceDerivative N f v z) q := by
  rw [sourceDerivative_eq_dir]
  exact source_readout_dir N f ((EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap) v z

/-- Literal mass of a projected original source in its real chart. -/
def characterMass (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) (w : ℂ) : ℝ :=
  ‖characterProjection N p r (sourceVector N f (ofComplex w))‖^(2 : ℕ)

/-- Literal physical gradient energy in one original character channel. -/
def characterGradient (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) (z : ℍ) : ℝ :=
  ‖characterProjection N p r (sourceDerivative N f 1 z)‖^(2 : ℕ)+
    ‖characterProjection N p r (sourceDerivative N f Complex.I z)‖^(2 : ℕ)

theorem characterMass_eq_sum (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) (w : ℂ) :
    characterMass N f p r w = ∑ q : Deck N, normSq (characterField N f p r q w) := by
  rw [characterMass,EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rfl

theorem characterMass_contDiffOn (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1)) :
    ContDiffOn ℝ 2 (characterMass N f p r) {z : ℂ | 0 < z.im} :=
  (((characterProjection N p r).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
    (sourceVector_contDiffOn N f)).norm_sq ℝ

/-- The full norm-square Laplacian of every actual projected source component. -/
theorem characterField_normSq_laplacian (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) (z : ℍ) :
    realLaplacian (fun w => normSq (characterField N f p r q w)) (z : ℂ) =
      2*(normSq (dir 1 (characterField N f p r q) (z : ℂ))+
        normSq (dir Complex.I (characterField N f p r q) (z : ℂ))-
        (lam/z.im^(2 : ℕ))*normSq (characterField N f p r q (z : ℂ))) := by
  have hf := (characterField_contDiffOn N f p r q).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have h := characterField_laplacian N f p r q z
  have hr := congrArg (fun c : ℂ => (c*(starRingEnd ℂ) (characterField N f p r q (z : ℂ))).re) h
  rw [add_mul,Complex.add_re,mul_assoc,Complex.mul_conj,← Complex.ofReal_mul,Complex.ofReal_re] at hr
  rw [realLaplacian,normSq_second_dir hf,normSq_second_dir hf]
  linarith

/-- Actual channel mass has the original spectral potential and complete projected gradient. -/
theorem characterMass_laplacian (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (z : ℍ) :
    realLaplacian (characterMass N f p r) (z : ℂ) =
      2*(characterGradient N f p r z-(lam/z.im^(2 : ℕ))*characterMass N f p r (z : ℂ)) := by
  have he : characterMass N f p r = (fun w => ∑ q : Deck N, normSq (characterField N f p r q w)) :=
    funext (characterMass_eq_sum N f p r)
  have hq (q : Deck N) : ContDiffAt ℝ 2 (fun w => normSq (characterField N f p r q w)) (z : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      ((characterField_contDiffOn N f p r q).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).norm_sq ℝ
  conv_lhs => rw [he,realLaplacian,second_dir_sum Finset.univ (fun q _ => hq q),
    second_dir_sum Finset.univ (fun q _ => hq q),← Finset.sum_add_distrib]
  change (∑ q : Deck N, realLaplacian (fun w => normSq (characterField N f p r q w)) (z : ℂ)) = _
  simp_rw [characterField_normSq_laplacian,characterField_dir]
  rw [characterGradient,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,characterMass_eq_sum]
  simp only [Complex.sq_norm,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]

/-- An actual character projector commutes with every motion in its complete block. -/
theorem characterProjection_commute_block (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (j : Multiplicative (ZMod (N+1))) (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N p r (finiteRegularUnitary (p j) v) =
      finiteRegularUnitary (p j) (characterProjection N p r v) := by
  ext q
  rw [finiteRegularUnitary_apply,characterProjection_coord,characterProjection_coord]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [finiteRegularUnitary_apply]
  have hc : p k * p j = p j * p k := by rw [← map_mul,← map_mul,mul_comm k j]
  rw [mul_assoc,mul_assoc,hc]

/-- The actual finite upper parameter one is the integral unit translation. -/
theorem upperBlock_one_eq_T :
    upperBlock N (Multiplicative.ofAdd (1 : ZMod (N+1))) = (QuotientGroup.mk T : Deck N) := by
  simpa only [Int.cast_one,SelbergMaassUnipotentPaths.upper_eq_T_zpow,zpow_one] using
    upperBlock_intCast N (1 : ℤ)

/-- Each actual upper-character mass has the unit translation symmetry of its original norm. -/
theorem characterMass_translation (r : ZMod (N+1)) (z : ℍ) :
    characterMass N f (upperBlock N) r ((T • z : ℍ) : ℂ) =
      characterMass N f (upperBlock N) r (z : ℂ) := by
  simp only [characterMass,ofComplex_apply,sourceVector_pullback]
  rw [← upperBlock_one_eq_T,characterProjection_commute_block,LinearIsometryEquiv.norm_map]

/-- Unit translation preserves the actual physical derivative of each upper-character mass. -/
theorem characterMass_current_translation (r : ZMod (N+1)) (v : ℂ) (z : ℍ) :
    dir v (characterMass N f (upperBlock N) r) ((T • z : ℍ) : ℂ) =
      dir v (characterMass N f (upperBlock N) r) (z : ℂ) := by
  have hd : sourceDerivative N f v (T • z) =
      finiteRegularUnitary (QuotientGroup.mk T : Deck N) (sourceDerivative N f v z) := by
    have h := sourceDerivative_modular N f T z v
    simpa [denom,ModularGroup.T] using h
  change dir v (fun w => ‖characterProjection N (upperBlock N) r (sourceVector N f (ofComplex w))‖^(2 : ℕ))
      ((T • z : ℍ) : ℂ) =
    dir v (fun w => ‖characterProjection N (upperBlock N) r (sourceVector N f (ofComplex w))‖^(2 : ℕ)) (z : ℂ)
  rw [character_mass_dir,character_mass_dir,sourceVector_pullback,hd,← upperBlock_one_eq_T,
    characterProjection_commute_block,LinearIsometryEquiv.inner_map_map]

/-- Literal upper-character currents match on the two actual vertical sides of the modular core. -/
theorem characterMass_current_sides (r : ZMod (N+1)) (v : ℂ) {y : ℝ} (hy : 0 < y) :
    dir v (characterMass N f (upperBlock N) r) (point (1/2) y) =
      dir v (characterMass N f (upperBlock N) r) (point (-(1/2)) y) := by
  have h := characterMass_current_translation N f r v (ofComplex (point (-(1/2)) y))
  rw [SelbergMaassTraceBoundary.translation_point _ hy] at h
  norm_num at h
  simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point _ hy] using h

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
