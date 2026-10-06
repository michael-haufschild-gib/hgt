import GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

/-!
# The cone extension: `K₁` of the open-history ideal and the exponential boundary

`K₁(J_T)` is realised as the homotopy classes of unitaries `u = λ + g(e)` of the unitization of
`J_T`, `g ∈ C_0((0,1))`.  The loop `t ↦ λ + g(t)` has modulus one, and its winding number

* is additive (`openWinding_mul`),
* is invariant along paths of such unitaries (`openWinding_eq_of_joinedIn`), and
* classifies them: equal winding numbers give a path (`joinedIn_of_openWinding_eq`; a unit loop
  `N` carries the unitary `N(0) + (N − N(0))(e)`).

The exponential `exp(2πi ρ(e))` of a real profile is the unitary of the loop `exp(2πi ρ(t))`,
of winding `ρ(1) − ρ(0)`.  Hence

* (SAC.8), (SAC.9) the connecting map `δ(n) = [exp(2πi n e_1)]` is an isomorphism `ℤ ≅ K₁(J_T)`
  and `δ(1)` winds once;
* (SAC.10) `exp(2πi e_c)` winds once for every scale `c`;
* (SAC.12) `exp(2πi(e_c − e_d))` is null-homotopic through `exp(2πi r(e_c − e_d))`;
* Corollary SAC-B: the integer classes are scale-blind while `‖e_c − e_d‖` is the sub-unit
  contrast, so no `K₁`-integer separates `c = d` from `c ≠ d`;
* the cone `C*(e_1) ≅ C_0((0,1])` is contractible through the dilations `g ↦ g(s ·)`.
-/

set_option autoImplicit false

open Filter Topology Set ContinuousLinearMap
open scoped ContinuousMapZero

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)

/-! ## Symbols of the open-history ideal -/

/-- The unitaries of the unitization of `J_T`, the representatives of `K₁(J_T)`. -/
def openHistoryUnitaries : Set (Unitization ℂ (BoundaryCorona H)) :=
  {u | u ∈ unitary (Unitization ℂ (BoundaryCorona H)) ∧ u.snd ∈ openHistoryIdeal hT hcpt}

open Classical in
/-- The symbol of an element of `C*(e)`: the function `g` with `g(e) = x` (zero off `C*(e)`). -/
def symbolOf (x : BoundaryCorona H) : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ :=
  if h : ∃ g, cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g = x then h.choose else 0

theorem symbolOf_cfcₙHom (g : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀) :
    symbolOf hT hcpt (cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g) = g := by
  have h : ∃ g', cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g' =
      cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g := ⟨g, rfl⟩
  rw [symbolOf, dif_pos h]
  exact cfcₙHom_injective (isStarNormal_unitGerm hT hcpt) h.choose_spec

variable (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

include hinj hH in
theorem cfcₙHom_symbolOf {x : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt) :
    cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) (symbolOf hT hcpt x) = x := by
  rw [openHistoryIdeal_eq_map hT hcpt hinj hH] at hx
  obtain ⟨g, -, hgx⟩ := hx
  have hgx' : cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g = x := hgx
  rw [← hgx', symbolOf_cfcₙHom]

include hinj hH in
theorem symbolOf_mem_endpointKernel {x : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt) :
    symbolOf hT hcpt x ∈ endpointKernel (one_mem_quasispectrum_unitGerm hT hcpt hinj hH) := by
  rw [openHistoryIdeal_eq_map hT hcpt hinj hH] at hx
  obtain ⟨g, hg, hgx⟩ := hx
  have hgx' : cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g = x := hgx
  rwa [← hgx', symbolOf_cfcₙHom]

/-- The point of `σ(e) = [0,1]` at the clamped parameter `t`. -/
def clampPoint (t : ℝ) : quasispectrum ℂ (unitGerm hT hcpt) :=
  ⟨((max 0 (min 1 t) : ℝ) : ℂ), by
    rw [quasispectrum_unitGerm hT hcpt hinj hH]
    exact ⟨_, clampUnit_re_mem (t : ℂ), by simp⟩⟩

theorem continuous_clampPoint : Continuous (clampPoint hT hcpt hinj hH) :=
  (Complex.continuous_ofReal.comp (continuous_const.max
    (continuous_const.min continuous_id))).subtype_mk _

theorem clampPoint_zero : (clampPoint hT hcpt hinj hH 0 : ℂ) = 0 := by simp [clampPoint]

theorem clampPoint_one : (clampPoint hT hcpt hinj hH 1 : ℂ) = 1 := by simp [clampPoint]

/-- The loop `t ↦ λ + g(t)` of an element `λ + g(e)` of the unitization of `J_T`. -/
def openLoop (u : Unitization ℂ (BoundaryCorona H)) (t : ℝ) : ℂ :=
  u.fst + symbolOf hT hcpt u.snd (clampPoint hT hcpt hinj hH t)

theorem continuous_openLoop (u : Unitization ℂ (BoundaryCorona H)) :
    Continuous (openLoop hT hcpt hinj hH u) :=
  continuous_const.add ((symbolOf hT hcpt u.snd).continuous.comp
    (continuous_clampPoint hT hcpt hinj hH))

/-! ## Unit-modulus loops and the winding index -/

include hinj hH in
/-- The symbol of a unitary of `J̃_T` satisfies `λ̄g + λḡ + |g|² = 0`. -/
theorem symbol_unitary_relation {u : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) :
    (starRingEnd ℂ) u.fst • symbolOf hT hcpt u.snd + u.fst • star (symbolOf hT hcpt u.snd) +
      star (symbolOf hT hcpt u.snd) * symbolOf hT hcpt u.snd = 0 := by
  obtain ⟨huu, hJ⟩ := hu
  have h1 : star u * u = 1 := Unitary.star_mul_self_of_mem huu
  have hsnd := congrArg (fun v : Unitization ℂ (BoundaryCorona H) => v.snd) h1
  simp only [Unitization.snd_mul, Unitization.fst_star, Unitization.snd_star,
    Unitization.snd_one] at hsnd
  have hx := cfcₙHom_symbolOf hT hcpt hinj hH hJ
  set Ψ := cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
  set g := symbolOf hT hcpt u.snd
  apply cfcₙHom_injective (isStarNormal_unitGerm hT hcpt)
  change Ψ _ = Ψ 0
  rw [map_zero, map_add, map_add, map_smul, map_smul, map_mul, map_star, hx]
  rw [← hsnd]
  simp only [Complex.star_def]

include hinj hH in
theorem openLoop_conj_mul_self {u : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) (t : ℝ) :
    (starRingEnd ℂ) (openLoop hT hcpt hinj hH u t) * openLoop hT hcpt hinj hH u t = 1 := by
  have hrel := congrArg (fun F : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ =>
    F (clampPoint hT hcpt hinj hH t)) (symbol_unitary_relation hT hcpt hinj hH hu)
  have hfst : (starRingEnd ℂ) u.fst * u.fst = 1 := by
    have h1 : star u * u = 1 := Unitary.star_mul_self_of_mem hu.1
    have := congrArg (fun v : Unitization ℂ (BoundaryCorona H) => v.fst) h1
    simpa using this
  simp only [ContinuousMapZero.coe_add, ContinuousMapZero.coe_smul, ContinuousMapZero.coe_mul,
    ContinuousMapZero.coe_star, ContinuousMapZero.coe_zero, Pi.add_apply, Pi.smul_apply,
    Pi.mul_apply, Pi.star_apply, Pi.zero_apply, smul_eq_mul, Complex.star_def] at hrel
  unfold openLoop
  rw [map_add]
  linear_combination hfst + hrel

include hinj hH in
theorem openLoop_isLoop {u : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) : IsLoop (openLoop hT hcpt hinj hH u) 0 1 := by
  refine ⟨continuous_openLoop hT hcpt hinj hH u, fun t h0 => ?_, ?_⟩
  · have := openLoop_conj_mul_self hT hcpt hinj hH hu t
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  · have hk := symbolOf_mem_endpointKernel hT hcpt hinj hH hu.2
    have hp0 : clampPoint hT hcpt hinj hH 0 = 0 := Subtype.ext (clampPoint_zero hT hcpt hinj hH)
    have hp1 : clampPoint hT hcpt hinj hH 1 = ⟨1, one_mem_quasispectrum_unitGerm hT hcpt hinj hH⟩ :=
      Subtype.ext (clampPoint_one hT hcpt hinj hH)
    unfold openLoop
    rw [hp0, hp1]
    have h0 : symbolOf hT hcpt u.snd 0 = 0 := (symbolOf hT hcpt u.snd).map_zero'
    rw [h0, show symbolOf hT hcpt u.snd ⟨1, one_mem_quasispectrum_unitGerm hT hcpt hinj hH⟩ = 0
      from hk]

/-- **The winding index** of a unitary of `J̃_T`: the winding number of `t ↦ λ + g(t)`. -/
def openWinding (u : Unitization ℂ (BoundaryCorona H)) : ℤ :=
  windingNumber (openLoop hT hcpt hinj hH u) 0 1

theorem mul_mem_openHistoryUnitaries {u v : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) (hv : v ∈ openHistoryUnitaries hT hcpt) :
    u * v ∈ openHistoryUnitaries hT hcpt := by
  refine ⟨mul_mem hu.1 hv.1, ?_⟩
  rw [Unitization.snd_mul]
  exact add_mem (add_mem ((openHistoryIdeal hT hcpt).smul_mem _ hv.2)
    ((openHistoryIdeal hT hcpt).smul_mem _ hu.2)) (mul_mem hu.2 hv.2)

include hinj hH in
theorem openLoop_mul {u v : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) (hv : v ∈ openHistoryUnitaries hT hcpt) (t : ℝ) :
    openLoop hT hcpt hinj hH (u * v) t =
      openLoop hT hcpt hinj hH u t * openLoop hT hcpt hinj hH v t := by
  have hx := cfcₙHom_symbolOf hT hcpt hinj hH hu.2
  have hy := cfcₙHom_symbolOf hT hcpt hinj hH hv.2
  set Ψ := cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
  have hsym : symbolOf hT hcpt (u * v).snd = u.fst • symbolOf hT hcpt v.snd +
      v.fst • symbolOf hT hcpt u.snd + symbolOf hT hcpt u.snd * symbolOf hT hcpt v.snd := by
    rw [Unitization.snd_mul, ← hx, ← hy, ← map_smul, ← map_smul, ← map_mul, ← map_add, ← map_add,
      symbolOf_cfcₙHom, hx, hy]
  unfold openLoop
  rw [hsym, Unitization.fst_mul]
  simp only [ContinuousMapZero.coe_add, ContinuousMapZero.coe_smul, ContinuousMapZero.coe_mul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

include hinj hH in
/-- **Additivity of the winding index.** -/
theorem openWinding_mul {u v : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) (hv : v ∈ openHistoryUnitaries hT hcpt) :
    openWinding hT hcpt hinj hH (u * v) =
      openWinding hT hcpt hinj hH u + openWinding hT hcpt hinj hH v := by
  unfold openWinding
  rw [show openLoop hT hcpt hinj hH (u * v) =
      fun t => openLoop hT hcpt hinj hH u t * openLoop hT hcpt hinj hH v t from
    funext (openLoop_mul hT hcpt hinj hH hu hv)]
  exact windingNumber_mul (openLoop_isLoop hT hcpt hinj hH hu) (openLoop_isLoop hT hcpt hinj hH hv)

/-! ## Homotopy invariance -/

include hinj hH in
/-- On `J_T` the symbol map is an isometry onto its image. -/
theorem dist_symbolOf {x y : BoundaryCorona H} (hx : x ∈ openHistoryIdeal hT hcpt)
    (hy : y ∈ openHistoryIdeal hT hcpt) :
    dist (symbolOf hT hcpt x) (symbolOf hT hcpt y) = dist x y := by
  have hiso := isometry_cfcₙHom (R := ℂ) _ (isStarNormal_unitGerm hT hcpt)
  rw [← hiso.dist_eq, cfcₙHom_symbolOf hT hcpt hinj hH hx, cfcₙHom_symbolOf hT hcpt hinj hH hy]

include hinj hH in
theorem continuous_symbolOf_comp {X : Type*} [TopologicalSpace X] {f : X → BoundaryCorona H}
    (hf : Continuous f) (hfJ : ∀ x, f x ∈ openHistoryIdeal hT hcpt) :
    Continuous fun x => symbolOf hT hcpt (f x) := by
  have hL : LipschitzOnWith 1 (symbolOf hT hcpt) (openHistoryIdeal hT hcpt) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_symbolOf hT hcpt hinj hH hx hy, NNReal.coe_one, one_mul]
  exact hL.continuousOn.comp_continuous hf hfJ

include hinj hH in
/-- **Homotopy invariance**: unitaries of `J̃_T` joined by a path of such unitaries have the same
winding index. -/
theorem openWinding_eq_of_joinedIn {u v : Unitization ℂ (BoundaryCorona H)}
    (h : JoinedIn (openHistoryUnitaries hT hcpt) u v) :
    openWinding hT hcpt hinj hH u = openWinding hT hcpt hinj hH v := by
  obtain ⟨γ, hγ⟩ := h
  have hmem : ∀ σ : ℝ, γ.extend σ ∈ openHistoryUnitaries hT hcpt := fun σ => hγ _
  have hu := hmem 0
  have hv := hmem 1
  rw [Path.extend_zero] at hu
  rw [Path.extend_one] at hv
  set Hm : ℝ → ℝ → ℂ := fun σ t => openLoop hT hcpt hinj hH (γ.extend σ) t
  have hsymc : Continuous fun σ : ℝ => symbolOf hT hcpt (γ.extend σ).snd :=
    continuous_symbolOf_comp hT hcpt hinj hH (Unitization.continuous_snd.comp γ.extend.continuous)
      fun σ => (hmem σ).2
  have hc : Continuous fun p : ℝ × ℝ => Hm p.1 p.2 := by
    refine (Unitization.continuous_fst.comp (γ.extend.continuous.comp continuous_fst)).add ?_
    exact continuous_eval.comp ((hsymc.comp continuous_fst).prodMk
      ((continuous_clampPoint hT hcpt hinj hH).comp continuous_snd))
  refine (windingNumber_eq_iff_joined (openLoop_isLoop hT hcpt hinj hH hu)
    (openLoop_isLoop hT hcpt hinj hH hv)).mpr ⟨Hm, hc, fun σ t => ?_, fun σ => ?_, fun t => ?_,
      fun t => ?_⟩
  · exact (openLoop_isLoop hT hcpt hinj hH (hmem σ)).nonzero t
  · exact (openLoop_isLoop hT hcpt hinj hH (hmem σ)).closed
  · simp only [Hm, Path.extend_zero]
  · simp only [Hm, Path.extend_one]

/-! ## Unitaries from unit-modulus loops -/

/-- The symbol `p ↦ N(re p) − N(0)` of a loop `N`. -/
def loopSymbol {N : ℝ → ℂ} (hN : Continuous N) : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ :=
  ⟨⟨fun p => N (p : ℂ).re - N 0, (hN.comp (Complex.continuous_re.comp continuous_subtype_val)).sub
    continuous_const⟩, by simp⟩

/-- The unitary `N(0) + (N − N(0))(e)` of `J̃_T` carried by a loop `N`. -/
def unitaryOfLoop {N : ℝ → ℂ} (hN : Continuous N) : Unitization ℂ (BoundaryCorona H) :=
  Unitization.inl (N 0) +
    (cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) (loopSymbol hT hcpt hN) :
      Unitization ℂ (BoundaryCorona H))

theorem unitaryOfLoop_fst {N : ℝ → ℂ} (hN : Continuous N) :
    (unitaryOfLoop hT hcpt hN).fst = N 0 := by
  simp [unitaryOfLoop]

theorem unitaryOfLoop_snd {N : ℝ → ℂ} (hN : Continuous N) :
    (unitaryOfLoop hT hcpt hN).snd =
      cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) (loopSymbol hT hcpt hN) := by
  simp [unitaryOfLoop]

include hinj hH in
/-- A loop of modulus one closing at `1` carries a unitary of `J̃_T`. -/
theorem unitaryOfLoop_mem {N : ℝ → ℂ} (hN : Continuous N)
    (hunit : ∀ t, (starRingEnd ℂ) (N t) * N t = 1) (hclosed : N 1 = N 0) :
    unitaryOfLoop hT hcpt hN ∈ openHistoryUnitaries hT hcpt := by
  set Ψ := cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt)
  set g := loopSymbol hT hcpt hN
  have hrel : (starRingEnd ℂ) (N 0) • g + N 0 • star g + star g * g = 0 := by
    ext p
    simp only [ContinuousMapZero.coe_add, ContinuousMapZero.coe_smul, ContinuousMapZero.coe_mul,
      ContinuousMapZero.coe_star, ContinuousMapZero.coe_zero, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, Pi.star_apply, Pi.zero_apply, smul_eq_mul, Complex.star_def]
    change (starRingEnd ℂ) (N 0) * (N (p : ℂ).re - N 0) +
      N 0 * (starRingEnd ℂ) (N (p : ℂ).re - N 0) +
      (starRingEnd ℂ) (N (p : ℂ).re - N 0) * (N (p : ℂ).re - N 0) = 0
    rw [map_sub]
    linear_combination hunit (p : ℂ).re - hunit 0
  have hrel' : N 0 • star g + (starRingEnd ℂ) (N 0) • g + g * star g = 0 := by
    ext p
    simp only [ContinuousMapZero.coe_add, ContinuousMapZero.coe_smul, ContinuousMapZero.coe_mul,
      ContinuousMapZero.coe_star, ContinuousMapZero.coe_zero, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, Pi.star_apply, Pi.zero_apply, smul_eq_mul, Complex.star_def]
    change N 0 * (starRingEnd ℂ) (N (p : ℂ).re - N 0) +
      (starRingEnd ℂ) (N 0) * (N (p : ℂ).re - N 0) +
      (N (p : ℂ).re - N 0) * (starRingEnd ℂ) (N (p : ℂ).re - N 0) = 0
    rw [map_sub]
    linear_combination hunit (p : ℂ).re - hunit 0
  have h1 : star (unitaryOfLoop hT hcpt hN) * unitaryOfLoop hT hcpt hN = 1 := by
    ext
    · simp [unitaryOfLoop_fst, hunit 0]
    · rw [Unitization.snd_mul, Unitization.fst_star, Unitization.snd_star, unitaryOfLoop_fst,
        unitaryOfLoop_snd, Unitization.snd_one, Complex.star_def, ← map_star Ψ g,
        ← map_smul Ψ, ← map_smul Ψ, ← map_mul Ψ, ← map_add Ψ, ← map_add Ψ, hrel, map_zero]
  have h2 : unitaryOfLoop hT hcpt hN * star (unitaryOfLoop hT hcpt hN) = 1 := by
    ext
    · simp only [Unitization.fst_mul, Unitization.fst_star, unitaryOfLoop_fst,
        Unitization.fst_one, Complex.star_def]
      rw [mul_comm]; exact hunit 0
    · rw [Unitization.snd_mul, Unitization.fst_star, Unitization.snd_star, unitaryOfLoop_fst,
        unitaryOfLoop_snd, Unitization.snd_one, Complex.star_def, ← map_star Ψ g,
        ← map_smul Ψ, ← map_smul Ψ, ← map_mul Ψ, ← map_add Ψ, ← map_add Ψ, hrel', map_zero]
  refine ⟨Unitary.mem_iff.mpr ⟨h1, h2⟩, ?_⟩
  rw [unitaryOfLoop_snd, openHistoryIdeal_eq_map hT hcpt hinj hH]
  refine ⟨g, ?_, rfl⟩
  change N ((1 : ℂ).re) - N 0 = 0
  rw [Complex.one_re, hclosed, sub_self]

theorem clampPoint_val (t : ℝ) :
    (clampPoint hT hcpt hinj hH t : ℂ) = ((max 0 (min 1 t) : ℝ) : ℂ) := rfl

include hinj hH in
theorem clampPoint_of_mem (p : quasispectrum ℂ (unitGerm hT hcpt)) :
    clampPoint hT hcpt hinj hH (p : ℂ).re = p := by
  obtain ⟨z, hz⟩ := p
  have hz' := hz
  rw [quasispectrum_unitGerm hT hcpt hinj hH] at hz'
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz'
  apply Subtype.ext
  simp [clampPoint_val, min_eq_right ht1, max_eq_right ht0]

include hinj hH in
theorem openLoop_unitaryOfLoop {N : ℝ → ℂ} (hN : Continuous N) (t : ℝ) :
    openLoop hT hcpt hinj hH (unitaryOfLoop hT hcpt hN) t = N (max 0 (min 1 t)) := by
  unfold openLoop
  rw [unitaryOfLoop_fst, unitaryOfLoop_snd, symbolOf_cfcₙHom]
  change N 0 + (N ((clampPoint hT hcpt hinj hH t : ℂ)).re - N 0) = _
  rw [clampPoint_val, Complex.ofReal_re]
  ring

include hinj hH in
theorem unitaryOfLoop_openLoop {u : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) :
    unitaryOfLoop hT hcpt (continuous_openLoop hT hcpt hinj hH u) = u := by
  have h0 : openLoop hT hcpt hinj hH u 0 = u.fst := by
    unfold openLoop
    have hp0 : clampPoint hT hcpt hinj hH 0 = 0 := Subtype.ext (clampPoint_zero hT hcpt hinj hH)
    have hz : symbolOf hT hcpt u.snd 0 = 0 := (symbolOf hT hcpt u.snd).map_zero'
    rw [hp0, hz, add_zero]
  ext
  · rw [unitaryOfLoop_fst, h0]
  · rw [unitaryOfLoop_snd]
    have hsym : loopSymbol hT hcpt (continuous_openLoop hT hcpt hinj hH u) =
        symbolOf hT hcpt u.snd := by
      ext p
      change openLoop hT hcpt hinj hH u (p : ℂ).re - openLoop hT hcpt hinj hH u 0 = _
      rw [h0]
      unfold openLoop
      rw [clampPoint_of_mem hT hcpt hinj hH p]
      ring
    rw [hsym, cfcₙHom_symbolOf hT hcpt hinj hH hu.2]

theorem unitaryOfLoop_congr {N N' : ℝ → ℂ} (hN : Continuous N) (hN' : Continuous N')
    (h : N = N') : unitaryOfLoop hT hcpt hN = unitaryOfLoop hT hcpt hN' := by
  subst h; rfl

/-! ## Completeness: the winding index classifies `K₁(J_T)` -/

theorem continuous_loopSymbol_family {N : ℝ → ℝ → ℂ}
    (hN : Continuous fun p : ℝ × ℝ => N p.1 p.2) :
    Continuous fun σ => loopSymbol hT hcpt (N := N σ)
      (hN.comp (continuous_const.prodMk continuous_id)) := by
  refine ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff.mpr ?_
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact (hN.comp (continuous_fst.prodMk (Complex.continuous_re.comp
    (continuous_subtype_val.comp continuous_snd)))).sub
      (hN.comp (continuous_fst.prodMk continuous_const))

theorem continuous_unitaryOfLoop_family {N : ℝ → ℝ → ℂ}
    (hN : Continuous fun p : ℝ × ℝ => N p.1 p.2) :
    Continuous fun σ => unitaryOfLoop hT hcpt (N := N σ)
      (hN.comp (continuous_const.prodMk continuous_id)) := by
  unfold unitaryOfLoop
  refine Continuous.add ?_ ?_
  · rw [show (fun σ => (Unitization.inl (N σ 0) : Unitization ℂ (BoundaryCorona H))) =
        fun σ => algebraMap ℂ (Unitization ℂ (BoundaryCorona H)) (N σ 0) from rfl]
    exact (continuous_algebraMap ℂ _).comp (hN.comp (continuous_id.prodMk continuous_const))
  · exact Unitization.continuous_inr.comp ((cfcₙHom_continuous (R := ℂ)
      (isStarNormal_unitGerm hT hcpt)).comp (continuous_loopSymbol_family hT hcpt hN))

theorem norm_eq_one_of_conj_mul_self {z : ℂ} (h : (starRingEnd ℂ) z * z = 1) : ‖z‖ = 1 := by
  have h2 : ‖z‖ ^ 2 = 1 := by
    have := congrArg Complex.re h
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at this
    exact this
  have := norm_nonneg z
  nlinarith

include hinj hH in
/-- **Completeness**: unitaries of `J̃_T` with the same winding index are joined by a path of
such unitaries. -/
theorem joinedIn_of_openWinding_eq {u v : Unitization ℂ (BoundaryCorona H)}
    (hu : u ∈ openHistoryUnitaries hT hcpt) (hv : v ∈ openHistoryUnitaries hT hcpt)
    (h : openWinding hT hcpt hinj hH u = openWinding hT hcpt hinj hH v) :
    JoinedIn (openHistoryUnitaries hT hcpt) u v := by
  obtain ⟨Hh, hc, hnv, hloop, hH0, hH1⟩ := (windingNumber_eq_iff_joined
    (openLoop_isLoop hT hcpt hinj hH hu) (openLoop_isLoop hT hcpt hinj hH hv)).mp h
  set Nn : ℝ → ℝ → ℂ := fun σ t => Hh σ t / ((‖Hh σ t‖ : ℝ) : ℂ)
  have hNc : Continuous fun p : ℝ × ℝ => Nn p.1 p.2 :=
    hc.div (Complex.continuous_ofReal.comp hc.norm) fun p => by
      exact_mod_cast (norm_pos_iff.mpr (hnv p.1 p.2)).ne'
  have hNunit : ∀ σ t, (starRingEnd ℂ) (Nn σ t) * Nn σ t = 1 := fun σ t => by
    have hne : ((‖Hh σ t‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr (hnv σ t)).ne'
    simp only [Nn, map_div₀, Complex.conj_ofReal]
    rw [div_mul_div_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← sq, div_self (by exact_mod_cast pow_ne_zero 2 hne)]
  have hNclosed : ∀ σ, Nn σ 1 = Nn σ 0 := fun σ => by simp only [Nn, hloop σ]
  have hcN : ∀ σ, Continuous (Nn σ) := fun σ => hNc.comp (continuous_const.prodMk continuous_id)
  have hendpoint : ∀ (w : Unitization ℂ (BoundaryCorona H)) (hw : w ∈ openHistoryUnitaries hT hcpt)
      (σ : ℝ), (∀ t, Hh σ t = openLoop hT hcpt hinj hH w t) →
      unitaryOfLoop hT hcpt (hcN σ) = w := fun w hw σ hσ => by
    have heq : Nn σ = openLoop hT hcpt hinj hH w := funext fun t => by
      simp only [Nn, hσ t,
        norm_eq_one_of_conj_mul_self (openLoop_conj_mul_self hT hcpt hinj hH hw t),
        Complex.ofReal_one, div_one]
    rw [unitaryOfLoop_congr hT hcpt (hcN σ) (continuous_openLoop hT hcpt hinj hH w) heq,
      unitaryOfLoop_openLoop hT hcpt hinj hH hw]
  let γ : Path u v :=
    { toFun := fun s => unitaryOfLoop hT hcpt (hcN s)
      continuous_toFun := (continuous_unitaryOfLoop_family hT hcpt hNc).comp continuous_subtype_val
      source' := hendpoint u hu 0 hH0
      target' := hendpoint v hv 1 hH1 }
  exact ⟨γ, fun s => unitaryOfLoop_mem hT hcpt hinj hH (hcN s) (hNunit s) (hNclosed s)⟩

/-! ## The exponential boundary map -/

/-- The exponential `exp(2πi a)` in the unitization of the corona. -/
def boundaryExp (a : BoundaryCorona H) : Unitization ℂ (BoundaryCorona H) :=
  NormedSpace.exp (((2 * Real.pi * Complex.I : ℂ)) • (a : Unitization ℂ (BoundaryCorona H)))

/-- `exp(2πi a) = 1 + (exp(2πi ·) − 1)(a)` for a normal `a`. -/
theorem boundaryExp_eq {a : BoundaryCorona H} (ha : IsStarNormal a) :
    boundaryExp a = 1 + ((cfcₙ (fun z => Complex.exp ((2 * Real.pi * Complex.I : ℂ) * z) - 1) a :
      BoundaryCorona H) : Unitization ℂ (BoundaryCorona H)) := by
  have ha' : IsStarNormal (a : Unitization ℂ (BoundaryCorona H)) := by
    have hc := ha.star_comm_self.map (Unitization.inrNonUnitalStarAlgHom ℂ (BoundaryCorona H))
    exact ⟨by simpa [map_star] using hc⟩
  rw [Unitization.complex_cfcₙ_eq_cfc_inr _ _ (by simp), boundaryExp,
    ← CFC.complex_exp_eq_normedSpace_exp (a := ((2 * Real.pi * Complex.I : ℂ)) •
      (a : Unitization ℂ (BoundaryCorona H))),
]
  have hcomp := cfc_comp_smul (S := ℂ) (2 * Real.pi * Complex.I : ℂ) Complex.exp
    (a : Unitization ℂ (BoundaryCorona H)) Complex.continuous_exp.continuousOn ha'
  have hadd := cfc_add (a : Unitization ℂ (BoundaryCorona H)) (fun _ => (1 : ℂ))
    (fun z => Complex.exp ((2 * Real.pi * Complex.I : ℂ) * z) - 1) continuousOn_const
    ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).sub
      continuous_const).continuousOn
  have hone : cfc (fun _ : ℂ => (1 : ℂ)) (a : Unitization ℂ (BoundaryCorona H)) = 1 :=
    cfc_one ℂ (a : Unitization ℂ (BoundaryCorona H)) ha'
  rw [← hcomp, ← hone, ← hadd]
  refine cfc_congr fun z _ => ?_
  simp [smul_eq_mul]

/-- The real functional calculus `ρ(e)` of a real profile `ρ` on `[0,1]`. -/
def profileElement (ρ : ℝ → ℝ) : BoundaryCorona H :=
  cfcₙ (fun z : ℂ => ((ρ z.re : ℝ) : ℂ)) (unitGerm hT hcpt)

theorem continuous_profileLoop {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    Continuous fun t : ℝ =>
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (ρ (max 0 (min 1 t)) : ℂ)) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (hρ.comp (continuous_const.max (continuous_const.min continuous_id)))))

include hinj hH in
/-- **The exponential boundary of a real profile**: `exp(2πi ρ(e))` is the unitary of `J̃_T`
carried by the loop `t ↦ exp(2πi ρ(t))`. -/
theorem boundaryExp_profileElement {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) :
    boundaryExp (profileElement hT hcpt ρ) = unitaryOfLoop hT hcpt (continuous_profileLoop hρ) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hn := isStarNormal_unitGerm hT hcpt
  have hρc : Continuous fun z : ℂ => ((ρ z.re : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hρ.comp Complex.continuous_re)
  have hsa : IsStarNormal (profileElement hT hcpt ρ) := by
    unfold profileElement
    exact IsStarNormal.cfcₙ_map _ _
  set E : ℂ → ℂ := fun z => Complex.exp ((2 * Real.pi * Complex.I : ℂ) * z) - 1
  have hEc : Continuous E := (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).sub
    continuous_const
  have hE0 : E 0 = 0 := by simp [E]
  rw [boundaryExp_eq hsa]
  unfold profileElement
  rw [← cfcₙ_comp E _ (unitGerm hT hcpt) hEc.continuousOn hE0 hρc.continuousOn (by simp [hρ0])]
  ext
  · simp [unitaryOfLoop_fst, hρ0]
  · rw [unitaryOfLoop_snd, Unitization.snd_add, Unitization.snd_one, zero_add,
      Unitization.snd_inr, cfcₙ_apply _ _ (hEc.comp hρc).continuousOn (by simp [E, hρ0])]
    congr 1
    ext p
    have hp : (p : ℂ) ∈ unitIntervalC := hσ ▸ p.2
    obtain ⟨t, ⟨ht0, ht1⟩, hpt⟩ := hp
    change E (((ρ (p : ℂ).re : ℝ) : ℂ)) = Complex.exp _ - Complex.exp _
    rw [← hpt, Complex.ofReal_re]
    simp [E, min_eq_right ht1, max_eq_right ht0, hρ0]

include hinj hH in
theorem unitaryOfLoop_profile_mem {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) {n : ℤ}
    (hn : ρ 1 - ρ 0 = n) :
    unitaryOfLoop hT hcpt (continuous_profileLoop hρ) ∈ openHistoryUnitaries hT hcpt := by
  refine unitaryOfLoop_mem hT hcpt hinj hH _ (fun t => ?_) ?_
  · set w : ℂ := (2 * Real.pi * Complex.I : ℂ) * (ρ (max 0 (min 1 t)) : ℂ)
    have hw : (starRingEnd ℂ) w = -w := by
      simp only [w, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [← Complex.exp_conj, hw, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero w)]
  · have h1 : max 0 (min 1 (1 : ℝ)) = 1 := by norm_num
    have h0 : max 0 (min 1 (0 : ℝ)) = 0 := by norm_num
    rw [h1, h0, hρ0]
    have : ρ 1 = n := by rw [← hn, hρ0, sub_zero]
    rw [this, Complex.ofReal_intCast, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (2 * Real.pi * Complex.I : ℂ) * n = n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n

include hinj hH in
/-- **Winding of a profile exponential**: if `ρ(1) − ρ(0) = n ∈ ℤ` then `exp(2πi ρ(e))` has
winding index `n`. -/
theorem openWinding_boundaryExp_profileElement {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0)
    {n : ℤ} (hn : ρ 1 - ρ 0 = n) :
    openWinding hT hcpt hinj hH (boundaryExp (profileElement hT hcpt ρ)) = n := by
  rw [boundaryExp_profileElement hT hcpt hinj hH hρ hρ0]
  have hmem := unitaryOfLoop_profile_mem hT hcpt hinj hH hρ hρ0 hn
  have hloop := openLoop_isLoop hT hcpt hinj hH hmem
  set L : ℝ → ℂ := fun t => (2 * Real.pi * Complex.I : ℂ) * (ρ (max 0 (min 1 t)) : ℂ)
  have hL : Continuous L := continuous_const.mul (Complex.continuous_ofReal.comp
    (hρ.comp (continuous_const.max (continuous_const.min continuous_id))))
  have hLe : ∀ t, Complex.exp (L t) = openLoop hT hcpt hinj hH
      (unitaryOfLoop hT hcpt (continuous_profileLoop hρ)) t := fun t => by
    rw [openLoop_unitaryOfLoop]
    simp only [L]
    congr 3
    rcases le_total t 0 with h | h
    · simp [h, min_eq_right (h.trans zero_le_one)]
    · rcases le_total t 1 with h' | h'
      · simp [min_eq_right h', max_eq_right h]
      · simp [min_eq_left h']
  have hinc := contLog_increment hloop hL hLe
  simp only [L] at hinc
  have h1 : max 0 (min 1 (1 : ℝ)) = 1 := by norm_num
  have h0 : max 0 (min 1 (0 : ℝ)) = 0 := by norm_num
  rw [h1, h0] at hinc
  unfold openWinding
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ((windingNumber (openLoop hT hcpt hinj hH
      (unitaryOfLoop hT hcpt (continuous_profileLoop hρ))) 0 1 : ℤ) : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [← hinc, ← mul_sub, ← Complex.ofReal_sub, hn, Complex.ofReal_intCast]
    ring
  exact_mod_cast key

/-! ## The scale germs as profiles -/

/-- The real scale change `φ_c(t) = ct/(1 + (c − 1)t)`. -/
def realScaleChange (c t : ℝ) : ℝ := c * t / (1 + (c - 1) * t)

theorem continuous_realScaleChange_clamp {c : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ => realScaleChange c (max 0 (min 1 t)) :=
  (continuous_const.mul (continuous_const.max (continuous_const.min continuous_id))).div
    (continuous_const.add (continuous_const.mul (continuous_const.max
      (continuous_const.min continuous_id)))) fun _ =>
        (scaleChange_denom_pos hc ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩).ne'

include hinj hH in
theorem scaleGerm_eq_profileElement {c : ℝ} (hc : 0 < c) :
    scaleGerm T hT hcpt hc =
      profileElement hT hcpt (fun t => realScaleChange c (max 0 (min 1 t))) := by
  rw [scaleGerm_eq_cfcₙ hT hcpt hinj hH hc, profileElement]
  refine cfcₙ_congr fun z hz => ?_
  rw [quasispectrum_unitGerm hT hcpt hinj hH] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  simp [scaleChange_ofReal, realScaleChange, min_eq_right ht1, max_eq_right ht0]

theorem realScaleChange_clamp_zero (c : ℝ) : realScaleChange c (max 0 (min 1 0)) = 0 := by
  simp [realScaleChange]

theorem realScaleChange_clamp_one {c : ℝ} (hc : 0 < c) :
    realScaleChange c (max 0 (min 1 1)) = 1 := by
  simp [realScaleChange, hc.ne']

include hinj hH in
/-- **(SAC.9), (SAC.10)**: for every scale `c`, the exponential `exp(2πi e_c)` of the lift `e_c` of
the endpoint unit is a unitary of `J̃_T` with winding index one. -/
theorem openWinding_boundaryExp_scaleGerm {c : ℝ} (hc : 0 < c) :
    boundaryExp (scaleGerm T hT hcpt hc) ∈ openHistoryUnitaries hT hcpt ∧
      openWinding hT hcpt hinj hH (boundaryExp (scaleGerm T hT hcpt hc)) = 1 := by
  have hρ := continuous_realScaleChange_clamp hc
  rw [scaleGerm_eq_profileElement hT hcpt hinj hH hc]
  refine ⟨?_, openWinding_boundaryExp_profileElement hT hcpt hinj hH hρ
    (realScaleChange_clamp_zero c) (n := 1) ?_⟩
  · rw [boundaryExp_profileElement hT hcpt hinj hH hρ (realScaleChange_clamp_zero c)]
    exact unitaryOfLoop_profile_mem hT hcpt hinj hH hρ (realScaleChange_clamp_zero c) (n := 1)
      (by simp only [realScaleChange_clamp_one hc, realScaleChange_clamp_zero]; norm_num)
  · simp only [realScaleChange_clamp_one hc, realScaleChange_clamp_zero]; norm_num

/-! ## `K₁(J_T) ≅ ℤ` and the connecting map -/

/-- `K₁(J_T)`: homotopy classes of unitaries of the unitization of `J_T`. -/
abbrev OpenK₁ := ZerothHomotopy (openHistoryUnitaries hT hcpt)

/-- The winding index on `K₁(J_T)`. -/
def openK₁Winding : OpenK₁ hT hcpt → ℤ :=
  Quotient.lift (fun u => openWinding hT hcpt hinj hH u.1) fun u v h =>
    openWinding_eq_of_joinedIn hT hcpt hinj hH ((joinedIn_iff_joined u.2 v.2).mpr h)

include hinj hH in
theorem openK₁Winding_injective : Function.Injective (openK₁Winding hT hcpt hinj hH) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h u => ?_
  induction y using Quotient.inductionOn with | h v => ?_
  exact Quotient.sound ((joinedIn_iff_joined u.2 v.2).mp
    (joinedIn_of_openWinding_eq hT hcpt hinj hH u.2 v.2 hxy))

theorem continuous_clamp_mul (n : ℤ) : Continuous fun t : ℝ => (n : ℝ) * max 0 (min 1 t) :=
  continuous_const.mul (continuous_const.max (continuous_const.min continuous_id))

include hinj hH in
theorem profileElement_clamp_mul (n : ℤ) :
    profileElement hT hcpt (fun t => (n : ℝ) * max 0 (min 1 t)) = (n : ℂ) • unitGerm hT hcpt := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hn := isStarNormal_unitGerm hT hcpt
  have hsm : (n : ℂ) • unitGerm hT hcpt = cfcₙ (fun z : ℂ => (n : ℂ) • z) (unitGerm hT hcpt) := by
    rw [cfcₙ_smul (n : ℂ) (fun z : ℂ => z) (unitGerm hT hcpt) continuousOn_id rfl,
      cfcₙ_id' ℂ _ hn]
  rw [profileElement, hsm]
  refine cfcₙ_congr fun z hz => ?_
  rw [hσ] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  simp [min_eq_right ht1, max_eq_right ht0]

include hinj hH in
theorem boundaryExp_intSMul_mem (n : ℤ) :
    boundaryExp ((n : ℂ) • unitGerm hT hcpt) ∈ openHistoryUnitaries hT hcpt := by
  rw [← profileElement_clamp_mul hT hcpt hinj hH n,
    boundaryExp_profileElement hT hcpt hinj hH (continuous_clamp_mul n) (by simp)]
  exact unitaryOfLoop_profile_mem hT hcpt hinj hH (continuous_clamp_mul n) (by simp) (n := n)
    (by simp)

/-- **The connecting map** `δ : K₀(ℂ) = ℤ → K₁(J_T)`, `δ(n) = [exp(2πi n e_1)]`: the exponential
of the positive contraction `e_1` lifting the endpoint unit. -/
def connectingMap (n : ℤ) : OpenK₁ hT hcpt :=
  ZerothHomotopy.mk ⟨boundaryExp ((n : ℂ) • unitGerm hT hcpt),
    boundaryExp_intSMul_mem hT hcpt hinj hH n⟩

include hinj hH in
theorem openK₁Winding_connectingMap (n : ℤ) :
    openK₁Winding hT hcpt hinj hH (connectingMap hT hcpt hinj hH n) = n := by
  change openWinding hT hcpt hinj hH (boundaryExp ((n : ℂ) • unitGerm hT hcpt)) = n
  rw [← profileElement_clamp_mul hT hcpt hinj hH n]
  exact openWinding_boundaryExp_profileElement hT hcpt hinj hH (continuous_clamp_mul n) (by simp)
    (by simp)

include hinj hH in
/-- **(SAC.8) The connecting map is an isomorphism** `ℤ ≅ K₁(J_T)`, inverse to the winding index,
and `δ(1)` winds once (SAC.9). -/
theorem connectingMap_bijective :
    Function.Bijective (connectingMap hT hcpt hinj hH) ∧
      Function.Bijective (openK₁Winding hT hcpt hinj hH) ∧
      openK₁Winding hT hcpt hinj hH (connectingMap hT hcpt hinj hH 1) = 1 := by
  have hleft : Function.LeftInverse (openK₁Winding hT hcpt hinj hH)
      (connectingMap hT hcpt hinj hH) := openK₁Winding_connectingMap hT hcpt hinj hH
  have hsurjW : Function.Surjective (openK₁Winding hT hcpt hinj hH) := hleft.surjective
  have hinjW := openK₁Winding_injective hT hcpt hinj hH
  refine ⟨⟨hleft.injective, fun x => ⟨openK₁Winding hT hcpt hinj hH x, hinjW ?_⟩⟩,
    ⟨hinjW, hsurjW⟩, openK₁Winding_connectingMap hT hcpt hinj hH 1⟩
  rw [openK₁Winding_connectingMap]

/-! ## The relative exponential and the direct-subunit no-go -/

theorem one_mem_openHistoryUnitaries : (1 : Unitization ℂ (BoundaryCorona H)) ∈
    openHistoryUnitaries hT hcpt :=
  ⟨one_mem _, by rw [Unitization.snd_one]; exact zero_mem _⟩

/-- The relative profile `φ_c − φ_d` on the clamped parameter. -/
def relativeProfile (c d t : ℝ) : ℝ :=
  realScaleChange c (max 0 (min 1 t)) - realScaleChange d (max 0 (min 1 t))

theorem continuous_relativeProfile {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Continuous (relativeProfile c d) :=
  (continuous_realScaleChange_clamp hc).sub (continuous_realScaleChange_clamp hd)

include hinj hH in
theorem scaleGerm_sub_eq_profileElement {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd =
      profileElement hT hcpt (relativeProfile c d) := by
  have hf1 : ContinuousOn (fun z : ℂ => ((realScaleChange c (max 0 (min 1 z.re)) : ℝ) : ℂ))
      (quasispectrum ℂ (unitGerm hT hcpt)) :=
    (Complex.continuous_ofReal.comp ((continuous_realScaleChange_clamp hc).comp
      Complex.continuous_re)).continuousOn
  have hf2 : ContinuousOn (fun z : ℂ => ((realScaleChange d (max 0 (min 1 z.re)) : ℝ) : ℂ))
      (quasispectrum ℂ (unitGerm hT hcpt)) :=
    (Complex.continuous_ofReal.comp ((continuous_realScaleChange_clamp hd).comp
      Complex.continuous_re)).continuousOn
  have hsub := cfcₙ_sub _ _ (unitGerm hT hcpt) hf1 (by simp [realScaleChange]) hf2
    (by simp [realScaleChange])
  rw [scaleGerm_eq_profileElement hT hcpt hinj hH hc,
    scaleGerm_eq_profileElement hT hcpt hinj hH hd, profileElement, profileElement,
    profileElement, ← hsub]
  refine cfcₙ_congr fun z _ => ?_
  simp [relativeProfile]

include hinj hH in
/-- **(SAC.12) The relative exponential is null-homotopic**: multiplying the self-adjoint exponent
by `r ∈ [0,1]` joins `exp(2πi(e_c − e_d))` to `1` through unitaries of `J̃_T`. -/
theorem joinedIn_boundaryExp_sub {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    JoinedIn (openHistoryUnitaries hT hcpt)
      (boundaryExp (scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd)) 1 := by
  set ρ := relativeProfile c d
  have hρ := continuous_relativeProfile hc hd
  have hρ0 : ρ 0 = 0 := by simp [ρ, relativeProfile, realScaleChange]
  have hρ1 : ρ 1 = 0 := by simp [ρ, relativeProfile, realScaleChange, hc.ne', hd.ne']
  set N : ℝ → ℝ → ℂ := fun r t =>
    Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (((1 - r) * ρ (max 0 (min 1 t)) : ℝ) : ℂ))
  have hNc : Continuous fun p : ℝ × ℝ => N p.1 p.2 :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.sub continuous_fst).mul (hρ.comp (continuous_const.max
        (continuous_const.min continuous_snd))))))
  have hcN : ∀ r, Continuous (N r) := fun r => hNc.comp (continuous_const.prodMk continuous_id)
  have hmem : ∀ r, unitaryOfLoop hT hcpt (hcN r) ∈ openHistoryUnitaries hT hcpt := fun r => by
    refine unitaryOfLoop_mem hT hcpt hinj hH (hcN r) (fun t => ?_) ?_
    · set w : ℂ := (2 * Real.pi * Complex.I : ℂ) * (((1 - r) * ρ (max 0 (min 1 t)) : ℝ) : ℂ)
      have hw : (starRingEnd ℂ) w = -w := by
        simp only [w, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
        ring
      change (starRingEnd ℂ) (Complex.exp w) * Complex.exp w = 1
      rw [← Complex.exp_conj, hw, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero w)]
    · have h1 : max 0 (min 1 (1 : ℝ)) = 1 := by norm_num
      have h0 : max 0 (min 1 (0 : ℝ)) = 0 := by norm_num
      simp only [N, h1, h0, hρ0, hρ1, mul_zero]
  have hstart : unitaryOfLoop hT hcpt (hcN 0) =
      boundaryExp (scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd) := by
    rw [scaleGerm_sub_eq_profileElement hT hcpt hinj hH hc hd,
      boundaryExp_profileElement hT hcpt hinj hH hρ hρ0]
    exact unitaryOfLoop_congr hT hcpt _ _ (funext fun t => by simp [N, ρ])
  have hend : unitaryOfLoop hT hcpt (hcN 1) = 1 := by
    have hconst : N 1 = fun _ => 1 := funext fun t => by simp [N]
    ext
    · rw [unitaryOfLoop_fst, Unitization.fst_one]; simp [N]
    · rw [unitaryOfLoop_snd, Unitization.snd_one]
      have hz : loopSymbol hT hcpt (hcN 1) = 0 := by
        ext p; simp [loopSymbol, N]
      rw [hz, map_zero]
  let γ : Path (boundaryExp (scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd)) 1 :=
    { toFun := fun s => unitaryOfLoop hT hcpt (hcN s)
      continuous_toFun := (continuous_unitaryOfLoop_family hT hcpt hNc).comp continuous_subtype_val
      source' := hstart
      target' := hend }
  exact ⟨γ, fun s => hmem s⟩

include hinj hH in
theorem boundaryExp_sub_mem {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    boundaryExp (scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd) ∈ openHistoryUnitaries hT hcpt :=
  (joinedIn_boundaryExp_sub hT hcpt hinj hH hc hd).mem.1

include hinj hH in
/-- **Corollary SAC-B (direct-subunit no-go).**  The universal endpoint index is scale-blind
(`exp(2πi e_c)` winds once for every `c`), the relative class of every two scale lifts is trivial
(`exp(2πi(e_c − e_d))` is null-homotopic), while the norm distance `‖e_c − e_d‖` is the sub-unit
contrast `|√c − √d|/(√c + √d)`, nonzero exactly when `c ≠ d`.  Consequently no integer invariant of
`K₁(J_T)` evaluated on the relative exponential distinguishes `c = d` from `c ≠ d`. -/
theorem directSubunit_noGo :
    (∀ (c : ℝ) (hc : 0 < c),
      openWinding hT hcpt hinj hH (boundaryExp (scaleGerm T hT hcpt hc)) = 1) ∧
    (∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      JoinedIn (openHistoryUnitaries hT hcpt)
        (boundaryExp (scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd)) 1) ∧
    (∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      ‖scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd‖ = |germContrast c d| ∧
        |germContrast c d| < 1 ∧ (germContrast c d = 0 ↔ c = d)) ∧
    (∀ (κ : OpenK₁ hT hcpt → ℤ) (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      κ (ZerothHomotopy.mk ⟨_, boundaryExp_sub_mem hT hcpt hinj hH hc hd⟩) =
        κ (ZerothHomotopy.mk ⟨1, one_mem_openHistoryUnitaries hT hcpt⟩)) := by
  refine ⟨fun c hc => (openWinding_boundaryExp_scaleGerm hT hcpt hinj hH hc).2,
    fun c d hc hd => joinedIn_boundaryExp_sub hT hcpt hinj hH hc hd,
    fun c d hc hd => ⟨norm_scaleGerm_sub hT hcpt hinj hH hc hd, abs_germContrast_lt_one hc hd,
      germContrast_eq_zero_iff hc.le hd.le (by linarith)⟩, fun κ c d hc hd => ?_⟩
  congr 1
  exact Quotient.sound ((joinedIn_iff_joined _ _).mp
    (joinedIn_boundaryExp_sub hT hcpt hinj hH hc hd))

/-! ## The cone is contractible -/

include hinj hH in
theorem smul_mem_quasispectrum_unitGerm (s : unitInterval)
    (p : quasispectrum ℂ (unitGerm hT hcpt)) :
    ((s : ℝ) : ℂ) * (p : ℂ) ∈ quasispectrum ℂ (unitGerm hT hcpt) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hp : (p : ℂ) ∈ unitIntervalC := hσ ▸ p.2
  obtain ⟨t, ⟨ht0, ht1⟩, hpt⟩ := hp
  have hmem : ((s : ℝ) : ℂ) * (p : ℂ) ∈ unitIntervalC := by
    refine ⟨(s : ℝ) * t, ⟨mul_nonneg s.2.1 ht0, mul_le_one₀ s.2.2 ht0 ht1⟩, ?_⟩
    rw [← hpt]; push_cast; ring
  rw [← hσ] at hmem
  exact hmem

/-- The dilation `t ↦ st` of the aperture interval. -/
def coneDilation (s : unitInterval) :
    C(quasispectrum ℂ (unitGerm hT hcpt), quasispectrum ℂ (unitGerm hT hcpt))₀ :=
  ⟨⟨fun p => ⟨((s : ℝ) : ℂ) * p, smul_mem_quasispectrum_unitGerm hT hcpt hinj hH s p⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩, Subtype.ext (by simp)⟩

/-- The contraction `g ↦ g(s ·)` of the cone `C_0((0,1]) ≅ C*(e_1)`. -/
def coneContraction (s : unitInterval) :
    C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ →⋆ₙₐ[ℂ] C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ :=
  ContinuousMapZero.nonUnitalStarAlgHom_precomp ℂ (coneDilation hT hcpt hinj hH s)

include hinj hH in
/-- **The cone `C*(e_1)` is contractible**: the dilations `g ↦ g(s ·)`, `s ∈ [0,1]`, form a
continuous path of `*`-endomorphisms from `0` to the identity. -/
theorem cone_contractible :
    (∀ g, coneContraction hT hcpt hinj hH 1 g = g) ∧
      (∀ g, coneContraction hT hcpt hinj hH 0 g = 0) ∧
      ∀ g, Continuous fun s => coneContraction hT hcpt hinj hH s g := by
  refine ⟨fun g => ?_, fun g => ?_, fun g => ?_⟩
  · ext p
    change g ⟨((1 : ℝ) : ℂ) * p, _⟩ = g p
    congr 1; exact Subtype.ext (by simp)
  · ext p
    change g ⟨((0 : ℝ) : ℂ) * p, _⟩ = 0
    have h0 : (⟨((0 : ℝ) : ℂ) * p, smul_mem_quasispectrum_unitGerm hT hcpt hinj hH 0 p⟩ :
        quasispectrum ℂ (unitGerm hT hcpt)) = 0 := Subtype.ext (by simp)
    rw [h0]; exact g.map_zero'
  · refine ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff.mpr ?_
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact g.continuous.comp ((((Complex.continuous_ofReal.comp continuous_subtype_val).comp
      continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

end GaloisForLFunctions.HTGeometry
