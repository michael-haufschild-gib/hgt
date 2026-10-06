import GaloisForLFunctions.HTGeometry.DeterminantLineHolomorphicBubbles
import GaloisForLFunctions.HTGeometry.DeterminantLineFillingHolonomy

/-!
# Closedness of the determinant-line Kähler form and the bubbling deck law

* Cubes `q ↦ P₊ + R(q)` of projections have six faces with boundary signs `(−1)^{i+ε}`; the
  boundary `∂R` is a cycle (`GrCube.bdry_bdryChain_eq_zero`: the 24 face edges pair off).
* `GrCube.kahlerIntegral_bdryChain` (**closedness**): `∫_{∂R} ω_det = 0`.  The boundary integral of
  the scaled cube `R(t ·)` is an integer (integrality on cycles), depends continuously on `t`, and
  vanishes at `t = 0`.
* The integral of `ω_det` over a chain depends only on the multiplicities of its non-degenerate
  squares (`GrChain.kahlerIntegral_eq_of_mult`).
* `GrChain.bubbling_deck_law`: if `c₀ ≡ c₁ + Σ_j B_j + ∂R` modulo degenerate squares, with
  holomorphic spheres `B_j` and a cubical `3`-chain `R`, then
  `∫_{c₀} ω_det = ∫_{c₁} ω_det + Σ_j m_j` with `m_j = ⟨c₁(L_det), [B_j]⟩ ∈ ℕ`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Pp : H →L[ℂ] H}

/-! ## Cubes and their boundaries -/

section Cube

/-- Insert the value `ε` into slot `i` of a point of the plane. -/
def cubeInsert : Fin 3 → ℝ → ℝ × ℝ → ℝ × ℝ × ℝ
  | 0, ε, q => (ε, q.1, q.2)
  | 1, ε, q => (q.1, ε, q.2)
  | 2, ε, q => (q.1, q.2, ε)

theorem contDiff_cubeInsert (i : Fin 3) (ε : ℝ) : ContDiff ℝ ⊤ (cubeInsert i ε) := by
  fin_cases i
  · exact contDiff_const.prodMk contDiff_id
  · exact contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  · exact contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)

variable (Pp) in
/-- A smooth cube `q ↦ P₊ + R(q)` of orthogonal projections in the restricted Grassmannian. -/
structure GrCube where
  /-- the Hilbert–Schmidt displacement `P − P₊` -/
  map : ℝ × ℝ × ℝ → SLSpace H
  smooth : ContDiff ℝ ⊤ map
  proj : ∀ q, IsStarProjection (Pp + (map q).op)

/-- The face `{xᵢ = ε}` of a cube. -/
def GrCube.face (R : GrCube Pp) (i : Fin 3) (ε : ℝ) : GrSquare Pp where
  map q := R.map (cubeInsert i ε q)
  smooth := R.smooth.comp (contDiff_cubeInsert i ε)
  proj _ := R.proj _

/-- The axis `i` of the `k`-th face `{xᵢ = ε}` of a cube. -/
def cubeFaceAxis : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

/-- The side `ε` of the `k`-th face `{xᵢ = ε}` of a cube. -/
def cubeFaceSide : Fin 6 → ℝ := ![0, 1, 0, 1, 0, 1]

/-- The boundary sign `(−1)^{i+ε}` of the `k`-th face (coordinates numbered from one). -/
def cubeFaceSign : Fin 6 → ℤ := ![-1, 1, 1, -1, -1, 1]

/-- The boundary of a cube: `∂R = Σᵢ Σ_ε (−1)^{i+ε} R|_{xᵢ = ε}`. -/
def GrCube.bdryChain (R : GrCube Pp) : GrChain Pp where
  len := 6
  coeff := cubeFaceSign
  sq k := R.face (cubeFaceAxis k) (cubeFaceSide k)

/-- The pairing of the `24` edges of the six faces of a cube: each edge of the cube is an edge of
exactly two faces. -/
def cubeEdgePair : Fin 6 × Fin 4 → Fin 6 × Fin 4 := fun x =>
  (![![(4, 3), (3, 3), (5, 3), (2, 3)], ![(4, 1), (3, 1), (5, 1), (2, 1)],
    ![(4, 0), (1, 3), (5, 0), (0, 3)], ![(4, 2), (1, 1), (5, 2), (0, 1)],
    ![(2, 0), (1, 0), (3, 0), (0, 0)], ![(2, 2), (1, 2), (3, 2), (0, 2)]] : Fin 6 → Fin 4 → _)
    x.1 x.2

theorem cubeEdgePair_involutive (x : Fin 6 × Fin 4) : cubeEdgePair (cubeEdgePair x) = x := by
  fin_cases x <;> rfl

theorem cubeEdgePair_ne (x : Fin 6 × Fin 4) : cubeEdgePair x ≠ x := by
  fin_cases x <;> decide

/-- Paired face edges coincide and carry opposite boundary signs. -/
theorem GrCube.edgePair (R : GrCube Pp) (x : Fin 6 × Fin 4) :
    (R.bdryChain.sq (cubeEdgePair x).1).edge (cubeEdgePair x).2 = (R.bdryChain.sq x.1).edge x.2 ∧
      R.bdryChain.coeff (cubeEdgePair x).1 * edgeSign (cubeEdgePair x).2 =
        -(R.bdryChain.coeff x.1 * edgeSign x.2) := by
  fin_cases x <;> exact ⟨rfl, rfl⟩

/-- **`∂∂ = 0`**: every edge of a cube occurs in two faces with opposite signs. -/
theorem GrCube.bdry_bdryChain_eq_zero (R : GrCube Pp) (e : ℝ → SLSpace H) :
    R.bdryChain.bdry e = 0 := by
  classical
  unfold GrChain.bdry GrChain.bdryOn
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun x _ => cubeEdgePair x) (fun x _ => ?_)
    (fun x _ _ => cubeEdgePair_ne x) (fun x _ => Finset.mem_univ _)
    (fun x _ => cubeEdgePair_involutive x)
  obtain ⟨hE, hs⟩ := R.edgePair x
  rw [hE, hs]
  split_ifs <;> simp

theorem GrCube.bdryChain_isCycle (R : GrCube Pp) : R.bdryChain.IsCycle :=
  fun e _ => R.bdry_bdryChain_eq_zero e

end Cube

/-! ## The integral of `ω_det` over the boundary of a cube vanishes -/

section Closed

theorem continuous_detKahlerForm_of {T : Type*} [TopologicalSpace T] {P : T → H →L[ℂ] H}
    {X Y : T → SLSpace H} (hP : Continuous P) (hX : Continuous X) (hY : Continuous Y) :
    Continuous fun t => detKahlerForm (P t) (X t).op (Y t).op := by
  have hX' : Continuous fun t => (X t).toHS := (slSubmodule H).subtypeL.continuous.comp hX
  have hY' : Continuous fun t => (Y t).toHS := (slSubmodule H).subtypeL.continuous.comp hY
  have heq : (fun t => detKahlerForm (P t) (X t).op (Y t).op) = fun t =>
      (HSpace.traceL (HSpace.lmulL (P t) (X t).toHS) (Y t).toHS -
        HSpace.traceL (HSpace.lmulL (P t) (Y t).toHS) (X t).toHS).im / (2 * Real.pi) := by
    funext t
    simp only [detKahlerForm, detCurvature, HSpace.traceL_apply, HSpace.op_lmulL]
    congr 2
    change opTrace (P t * ((X t).op * (Y t).op - (Y t).op * (X t).op)) =
      opTrace (P t * (X t).op * (Y t).op) - opTrace (P t * (Y t).op * (X t).op)
    rw [mul_sub, ← mul_assoc, ← mul_assoc]
    exact opTrace_sub_of_mem (mul_mem_hsTraceIdeal ((X t).isHS.comp_left _) (Y t).isHS)
      (mul_mem_hsTraceIdeal ((Y t).isHS.comp_left _) (X t).isHS)
  rw [heq]
  have hA : Continuous fun t => HSpace.lmulL (P t) (X t).toHS :=
    (HSpace.lmulL.continuous.comp hP).clm_apply hX'
  have hB : Continuous fun t => HSpace.lmulL (P t) (Y t).toHS :=
    (HSpace.lmulL.continuous.comp hP).clm_apply hY'
  exact (Complex.continuous_im.comp (((HSpace.traceL.continuous.comp hA).clm_apply hY').sub
    ((HSpace.traceL.continuous.comp hB).clm_apply hX'))).div_const _

theorem continuous_parametric_unitSquare {G : ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) :
    Continuous fun t => ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, G t (x, y) := by
  have h1 : Continuous fun p : ℝ × ℝ => ∫ y in (0 : ℝ)..1, G p.1 (p.2, y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : ℝ × ℝ) (y : ℝ) => G p.1 (p.2, y))
      (hG.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 1
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t x => ∫ y in (0 : ℝ)..1, G t (x, y)) h1 0 1

/-- A continuous integer-valued function on the line that vanishes at `0` vanishes at `1`. -/
theorem eq_zero_of_continuous_of_forall_int {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ t, ∃ n : ℤ, f t = n) (h0 : f 0 = 0) : f 1 = 0 := by
  obtain ⟨n, hn⟩ := hint 1
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by rw [hn, h, Int.cast_zero])
  have half : ∀ m : ℤ, (m : ℝ) ≠ 1 / 2 ∧ (m : ℝ) ≠ -1 / 2 := fun m => by
    constructor <;> intro h
    · have : (2 * m : ℝ) = 1 := by linarith
      have : 2 * m = 1 := by exact_mod_cast this
      omega
    · have : (2 * m : ℝ) = -1 := by linarith
      have : 2 * m = -1 := by exact_mod_cast this
      omega
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have hle : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    have hmem : (-1 / 2 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
      rw [h0, hn]; constructor <;> linarith
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
    obtain ⟨m, hm⟩ := hint t
    exact (half m).2 (hm ▸ ht)
  · have hle : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have hmem : (1 / 2 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
      rw [h0, hn]; constructor <;> linarith
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmem
    obtain ⟨m, hm⟩ := hint t
    exact (half m).1 (hm ▸ ht)

/-- The cube scaled towards the origin, `q ↦ R(t q)`. -/
def GrCube.scale (R : GrCube Pp) (t : ℝ) : GrCube Pp where
  map q := R.map (t • q)
  smooth := R.smooth.comp (contDiff_id.const_smul t)
  proj _ := R.proj _

theorem GrCube.scale_one (R : GrCube Pp) : R.scale 1 = R := by
  cases R
  simp [GrCube.scale]

theorem GrCube.kahlerIntegral_bdryChain_eq (R : GrCube Pp) :
    R.bdryChain.kahlerIntegral = ∑ k : Fin 6, (cubeFaceSign k : ℝ) *
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareKahler Pp (R.face (cubeFaceAxis k) (cubeFaceSide k)).map (x, y) := rfl

theorem squareKahler_const (c : SLSpace H) (q : ℝ × ℝ) :
    squareKahler Pp (fun _ => c) q = 0 := by
  simp [squareKahler, detKahlerForm, detCurvature, opTrace]

/-- **Closedness of `ω_det` on cubes**: the integral of `ω_det` over the boundary of every cube
vanishes.  The boundary integral of the scaled cube `R(t ·)` is an integer (the boundary is a
cycle), depends continuously on `t`, and vanishes for the constant cube `t = 0`. -/
theorem GrCube.kahlerIntegral_bdryChain (R : GrCube Pp) : R.bdryChain.kahlerIntegral = 0 := by
  set φ : ℝ → ℝ := fun t => (R.scale t).bdryChain.kahlerIntegral
  have hcont : Continuous φ := by
    have hφ : φ = fun t => ∑ k : Fin 6, (cubeFaceSign k : ℝ) * ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1, squareKahler Pp (fun q => R.map (t • cubeInsert (cubeFaceAxis k)
          (cubeFaceSide k) q)) (x, y) := by
      funext t; simp only [φ]; exact (R.scale t).kahlerIntegral_bdryChain_eq
    rw [hφ]
    refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
    refine continuous_parametric_unitSquare (G := fun t q => squareKahler Pp
      (fun q => R.map (t • cubeInsert (cubeFaceAxis k) (cubeFaceSide k) q)) q) ?_
    have hsm : ContDiff ℝ ⊤ (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (q : ℝ × ℝ) =>
        R.map (p.1 • cubeInsert (cubeFaceAxis k) (cubeFaceSide k) q)) :=
      R.smooth.comp ((contDiff_fst.fst).smul
        ((contDiff_cubeInsert (cubeFaceAxis k) (cubeFaceSide k)).comp contDiff_snd))
    have hD : Continuous fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ (fun q => R.map (p.1 • cubeInsert (cubeFaceAxis k) (cubeFaceSide k) q)) p.2 :=
      (hsm.fderiv (n := 0) contDiff_snd (by simp)).continuous
    refine continuous_detKahlerForm_of ?_ (hD.clm_apply continuous_const)
      (hD.clm_apply continuous_const)
    exact continuous_const.add ((SLSpace.opCLM H).continuous.comp (hsm.continuous.comp
      (continuous_id.prodMk continuous_snd)))
  have hint : ∀ t, ∃ n : ℤ, φ t = n := fun t =>
    (R.scale t).bdryChain.kahlerIntegral_mem_int (R.scale t).bdryChain_isCycle
  have h0 : φ 0 = 0 := by
    simp only [φ, GrCube.kahlerIntegral_bdryChain_eq]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hc : (R.scale 0).face (cubeFaceAxis k) (cubeFaceSide k) =
        ⟨fun _ => R.map 0, contDiff_const, fun _ => R.proj 0⟩ := by
      simp [GrCube.face, GrCube.scale]
    rw [hc]
    simp [squareKahler_const]
  have h1 := eq_zero_of_continuous_of_forall_int hcont hint h0
  simpa [φ, GrCube.scale_one] using h1

end Closed


/-! ## Chain algebra and multiplicities -/

section Algebra

/-- The zero chain. -/
def GrChain.zero : GrChain Pp := ⟨0, Fin.elim0, Fin.elim0⟩

/-- An integer multiple of a chain. -/
def GrChain.smul (a : ℤ) (c : GrChain Pp) : GrChain Pp := ⟨c.len, fun k => a * c.coeff k, c.sq⟩

/-- The sum of a list of chains. -/
def GrChain.sumList (L : List (GrChain Pp)) : GrChain Pp := L.foldr GrChain.add GrChain.zero

/-- The boundary `Σ aᵢ ∂Rᵢ` of a cubical `3`-chain `Σ aᵢ Rᵢ`. -/
def cubeChainBdry (R : List (ℤ × GrCube Pp)) : GrChain Pp :=
  GrChain.sumList (R.map fun p => p.2.bdryChain.smul p.1)

theorem GrChain.kahlerIntegral_zero : (GrChain.zero : GrChain Pp).kahlerIntegral = 0 := by
  simp [GrChain.zero, GrChain.kahlerIntegral, GrChain.kahlerOn]

theorem GrChain.kahlerIntegral_smul (a : ℤ) (c : GrChain Pp) :
    (c.smul a).kahlerIntegral = a * c.kahlerIntegral := by
  simp only [GrChain.kahlerIntegral, GrChain.kahlerOn, GrChain.smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem GrChain.kahlerIntegral_sumList (L : List (GrChain Pp)) :
    (GrChain.sumList L).kahlerIntegral = (L.map GrChain.kahlerIntegral).sum := by
  induction L with
  | nil => exact GrChain.kahlerIntegral_zero
  | cons c L ih =>
    simp only [GrChain.sumList, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [GrChain.kahlerIntegral_add, ih]

theorem kahlerIntegral_cubeChainBdry (R : List (ℤ × GrCube Pp)) :
    (cubeChainBdry R).kahlerIntegral = 0 := by
  rw [cubeChainBdry, GrChain.kahlerIntegral_sumList]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
  rw [GrChain.kahlerIntegral_smul, p.2.kahlerIntegral_bdryChain, mul_zero]

open Classical in
/-- The multiplicity of a square in a chain. -/
def GrChain.mult (c : GrChain Pp) (S : GrSquare Pp) : ℤ :=
  ∑ k, if c.sq k = S then c.coeff k else 0

theorem GrChain.mult_add (c c' : GrChain Pp) (S : GrSquare Pp) :
    (c.add c').mult S = c.mult S + c'.mult S := by
  unfold GrChain.mult
  change ∑ k : Fin (c.len + c'.len), _ = _
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_
  · have h1 : (c.add c').sq (Fin.castAdd c'.len k) = c.sq k := Fin.append_left _ _ _
    have h2 : (c.add c').coeff (Fin.castAdd c'.len k) = c.coeff k := Fin.append_left _ _ _
    rw [h2]; split_ifs with ha hb hb <;> first | rfl | (rw [h1] at ha; contradiction)
  · have h1 : (c.add c').sq (Fin.natAdd c.len k) = c'.sq k := Fin.append_right _ _ _
    have h2 : (c.add c').coeff (Fin.natAdd c.len k) = c'.coeff k := Fin.append_right _ _ _
    rw [h2]; split_ifs with ha hb hb <;> first | rfl | (rw [h1] at ha; contradiction)

/-- The determinant-line integral over a single square. -/
def squareIntegral (S : GrSquare Pp) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp S.map (x, y)

/-- A degenerate square: independent of one of its coordinates. -/
def GrSquare.IsDegenerate (S : GrSquare Pp) : Prop :=
  (∀ x y, S.map (x, y) = S.map (0, y)) ∨ ∀ x y, S.map (x, y) = S.map (x, 0)

theorem GrSquare.squareIntegral_eq_zero (S : GrSquare Pp) (hS : S.IsDegenerate) :
    squareIntegral S = 0 := by
  have hdiff : Differentiable ℝ S.map := S.smooth.differentiable (by simp)
  have hpt : ∀ q, squareKahler Pp S.map q = 0 := by
    intro q
    rcases hS with h | h
    · have hf : S.map = S.map ∘ fun q : ℝ × ℝ => ((0 : ℝ), q.2) := funext fun q => h q.1 q.2
      have hX : fderiv ℝ S.map q (1, 0) = 0 := by
        rw [hf, fderiv_comp q (hdiff _) ((differentiable_const _).prodMk differentiable_snd _)]
        have hd : HasFDerivAt (fun q : ℝ × ℝ => ((0 : ℝ), q.2))
            ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
          (hasFDerivAt_const (0 : ℝ) q).prodMk (hasFDerivAt_snd (p := q))
        simp [hd.fderiv, ← Prod.zero_eq_mk]
      simp [squareKahler, hX, detKahlerForm, detCurvature, opTrace]
    · have hf : S.map = S.map ∘ fun q : ℝ × ℝ => (q.1, (0 : ℝ)) := funext fun q => h q.1 q.2
      have hY : fderiv ℝ S.map q (0, 1) = 0 := by
        rw [hf, fderiv_comp q (hdiff _) (differentiable_fst.prodMk (differentiable_const _) _)]
        have hd : HasFDerivAt (fun q : ℝ × ℝ => (q.1, (0 : ℝ)))
            ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : ℝ × ℝ →L[ℝ] ℝ)) q :=
          (hasFDerivAt_fst (p := q)).prodMk (hasFDerivAt_const (0 : ℝ) q)
        simp [hd.fderiv, ← Prod.zero_eq_mk]
      simp [squareKahler, hY, detKahlerForm, detCurvature, opTrace]
  simp [squareIntegral, hpt]

/-- The integral of a chain regrouped by squares. -/
theorem GrChain.kahlerIntegral_eq_sum_mult (c : GrChain Pp) [DecidableEq (GrSquare Pp)]
    (T : Finset (GrSquare Pp)) (hT : ∀ k, c.sq k ∈ T) :
    c.kahlerIntegral = ∑ S ∈ T, (c.mult S : ℝ) * squareIntegral S := by
  classical
  unfold GrChain.kahlerIntegral GrChain.kahlerOn GrChain.mult
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (c.sq k)]
  · rw [if_pos rfl]; rfl
  · intro S _ hne
    rw [if_neg (Ne.symm hne), Int.cast_zero, zero_mul]
  · intro h; exact absurd (hT k) h

/-- **The integral of `ω_det` depends only on the multiplicities of non-degenerate squares.** -/
theorem GrChain.kahlerIntegral_eq_of_mult (c c' : GrChain Pp)
    (h : ∀ S : GrSquare Pp, ¬ S.IsDegenerate → c.mult S = c'.mult S) :
    c.kahlerIntegral = c'.kahlerIntegral := by
  classical
  set T := Finset.univ.image c.sq ∪ Finset.univ.image c'.sq
  rw [c.kahlerIntegral_eq_sum_mult T fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _
    (Finset.mem_univ k)), c'.kahlerIntegral_eq_sum_mult T fun k => Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : S.IsDegenerate
  · rw [S.squareIntegral_eq_zero hS, mul_zero, mul_zero]
  · rw [h S hS]

end Algebra

/-! ## Degeneration into a residual filling and holomorphic bubbles -/

section Degeneration

/-- The degree of a holomorphic sphere as a natural number. -/
def HolSphere.natDegree (B : HolSphere Pp) : ℕ := B.exists_degree_eq_nat.choose

theorem HolSphere.degree_eq_natDegree (B : HolSphere Pp) : B.degree = B.natDegree :=
  B.exists_degree_eq_nat.choose_spec

/-- The chain `Σ_j B_j` of a list of holomorphic spheres. -/
def bubbleChain (bubbles : List (HolSphere Pp)) : GrChain Pp :=
  GrChain.sumList (bubbles.map HolSphere.chain)

theorem kahlerIntegral_bubbleChain (bubbles : List (HolSphere Pp)) :
    (bubbleChain bubbles).kahlerIntegral = ((bubbles.map HolSphere.natDegree).sum : ℝ) := by
  rw [bubbleChain, GrChain.kahlerIntegral_sumList, List.map_map]
  push_cast [List.map_map]
  congr 1
  exact List.map_congr_left fun B _ => B.degree_eq_natDegree

/-- **The bubbling deck law.**  If a filling `c₀` degenerates to a residual filling `c₁` plus
holomorphic sphere bubbles `B_j`, i.e. `c₀ ≡ c₁ + Σ_j B_j + ∂R` modulo degenerate squares for a
cubical `3`-chain `R`, then every bubble degree `m_j = ⟨c₁(L_det), [B_j]⟩` is a natural number and
`∫_{c₀} ω_det = ∫_{c₁} ω_det + Σ_j m_j`; in particular the deck integer is `Σ_j m_j ≥ 0`. -/
theorem GrChain.bubbling_deck_law (c₀ c₁ : GrChain Pp) (bubbles : List (HolSphere Pp))
    (R : List (ℤ × GrCube Pp))
    (hdeg : ∀ S : GrSquare Pp, ¬ S.IsDegenerate →
      c₀.mult S = c₁.mult S + (bubbleChain bubbles).mult S + (cubeChainBdry R).mult S) :
    c₀.kahlerIntegral = c₁.kahlerIntegral + ((bubbles.map HolSphere.natDegree).sum : ℝ) ∧
      0 ≤ c₀.kahlerIntegral - c₁.kahlerIntegral := by
  have h := c₀.kahlerIntegral_eq_of_mult ((c₁.add (bubbleChain bubbles)).add (cubeChainBdry R))
    fun S hS => by rw [GrChain.mult_add, GrChain.mult_add, hdeg S hS]
  rw [GrChain.kahlerIntegral_add, GrChain.kahlerIntegral_add, kahlerIntegral_cubeChainBdry,
    kahlerIntegral_bubbleChain, add_zero] at h
  refine ⟨h, ?_⟩
  rw [h, add_sub_cancel_left]
  positivity

end Degeneration

end

end GaloisForLFunctions.HTGeometry
