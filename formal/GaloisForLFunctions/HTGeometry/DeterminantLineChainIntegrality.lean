import GaloisForLFunctions.HTGeometry.DeterminantLineSquareHolonomy

/-!
# Integrality of the determinant-line Kähler form on cycles

Squares in the restricted Grassmannian are smooth maps `q ↦ P₊ + C(q)` of orthogonal projections;
cubical `2`-chains are finite families of squares with integer multiplicities, and their boundary
multiplicity counts the edges `bottom + right − top − left`.  A cycle has vanishing boundary on every
non-degenerate path.

* `GrSquare.inSector_of_mem`: a square with one point in an admissible sector lies in it.
* `exp_kahlerOn_eq_one`: within one sector, `exp(2πi ∫_c ω_det)` is the product of the edge
  holonomies raised to the boundary multiplicities, hence `1` on cycles.
* `GrChain.kahlerIntegral_mem_int` (**integrality of `c₁` of the determinant line**): for every
  cycle, `∫_c ω_det ∈ ℤ`; the proof peels off one sector at a time.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Squares and chains in the restricted Grassmannian -/

variable (Pp : H →L[ℂ] H)

/-- A smooth square of orthogonal projections `q ↦ P₊ + C(q)` in the restricted Grassmannian. -/
structure GrSquare where
  /-- the Hilbert–Schmidt displacement `P − P₊` -/
  map : ℝ × ℝ → SLSpace H
  smooth : ContDiff ℝ ⊤ map
  proj : ∀ q, IsStarProjection (Pp + (map q).op)

/-- A cubical `2`-chain: finitely many squares with integer multiplicities. -/
structure GrChain where
  /-- the number of squares -/
  len : ℕ
  /-- the multiplicities -/
  coeff : Fin len → ℤ
  /-- the squares -/
  sq : Fin len → GrSquare Pp

variable {Pp}

/-- The four edges of a square: bottom, right, top, left. -/
def GrSquare.edge (S : GrSquare Pp) : Fin 4 → ℝ → SLSpace H
  | 0 => hLine S.map 0
  | 1 => vLine S.map 1
  | 2 => hLine S.map 1
  | 3 => vLine S.map 0

/-- The orientation signs of the edges in `∂ = bottom + right − top − left`. -/
def edgeSign : Fin 4 → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | 3 => -1

open Classical in
/-- The boundary multiplicity of a path in the sub-chain indexed by `T`. -/
def GrChain.bdryOn (c : GrChain Pp) (T : Finset (Fin c.len)) (e : ℝ → SLSpace H) : ℤ :=
  ∑ k ∈ T, ∑ j : Fin 4, if (c.sq k).edge j = e then c.coeff k * edgeSign j else 0

/-- The boundary multiplicity of a path in a chain. -/
def GrChain.bdry (c : GrChain Pp) (e : ℝ → SLSpace H) : ℤ := c.bdryOn Finset.univ e

/-- A degenerate (constant) path. -/
def IsDegeneratePath (e : ℝ → SLSpace H) : Prop := ∀ τ, e τ = e 0

/-- A cycle: the boundary vanishes on every non-degenerate path. -/
def GrChain.IsCycle (c : GrChain Pp) : Prop :=
  ∀ e, ¬ IsDegeneratePath e → c.bdry e = 0

/-- The determinant-line Kähler density of a square, `ω_det(∂ₛP, ∂ₜP)`. -/
def squareKahler (Pp : H →L[ℂ] H) (C : ℝ × ℝ → SLSpace H) (q : ℝ × ℝ) : ℝ :=
  detKahlerForm (Pp + (C q).op) (fderiv ℝ C q (1, 0)).op (fderiv ℝ C q (0, 1)).op

/-- The integral of `ω_det` over the sub-chain indexed by `T`. -/
def GrChain.kahlerOn (c : GrChain Pp) (T : Finset (Fin c.len)) : ℝ :=
  ∑ k ∈ T, (c.coeff k : ℝ) * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    squareKahler Pp (c.sq k).map (x, y)

/-- The integral `∫_c ω_det` of the determinant-line Kähler form over a chain. -/
def GrChain.kahlerIntegral (c : GrChain Pp) : ℝ := c.kahlerOn Finset.univ

theorem squareCurvature_eq (S : GrSquare Pp) (q : ℝ × ℝ) :
    squareCurvature Pp S.map q = 2 * Real.pi * Complex.I * squareKahler Pp S.map q :=
  detCurvature_eq_two_pi_I_mul (S.proj q).isSelfAdjoint (fderiv ℝ S.map q (1, 0)).isSelfAdjoint
    (fderiv ℝ S.map q (0, 1)).isSelfAdjoint (fderiv ℝ S.map q (1, 0)).isHS
    (fderiv ℝ S.map q (0, 1)).isHS

theorem integral_squareCurvature_eq_kahler (S : GrSquare Pp) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareCurvature Pp S.map (x, y) =
      2 * Real.pi * Complex.I * ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareKahler Pp S.map (x, y) : ℝ) : ℂ) := by
  simp_rw [squareCurvature_eq, intervalIntegral.integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  congr 1; funext x
  rw [← intervalIntegral.integral_ofReal]


/-! ## Sectors of squares -/

section Sector

variable {Q : H →L[ℂ] H}

/-- All points of the unit square carry admissible frames relative to `Q`. -/
def GrSquare.InSector (Q : H →L[ℂ] H) (S : GrSquare Pp) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, ∃ u, IsAdmissibleFrame Q u (Pp + (S.map q).op)

/-- **A square with one point in the admissible sector lies in it.** -/
theorem GrSquare.inSector_of_mem (hQ : IsStarProjection Q) (S : GrSquare Pp) {q₀ : ℝ × ℝ}
    (hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (h₀ : ∃ u, IsAdmissibleFrame Q u (Pp + (S.map q₀).op)) : S.InSector Q := by
  intro q hq
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    (convex_Icc 0 1).prod (convex_Icc 0 1)
  refine exists_admissibleFrame_of_isPreconnected hQ hconv.isPreconnected
    (P := fun q => Pp + (S.map q).op)
    (continuous_const.add ((SLSpace.opCLM H).continuous.comp S.smooth.continuous)).continuousOn
    (fun q _ => S.proj q) (fun x _ y _ => ?_) hq₀ hq h₀
  have : Pp + (S.map x).op - (Pp + (S.map y).op) = (S.map x - S.map y).op := by
    rw [SLSpace.op_sub]; abel
  rw [this]; exact (S.map x - S.map y).isHS

end Sector

/-! ## Regrouping products by edges -/

section Regroup

theorem zpow_finset_sum {G : Type*} [CommGroup G] {ι : Type*} (a : G) (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem prod_regroup {G : Type*} [CommGroup G] {ι α : Type*} [DecidableEq α] (T : Finset ι)
    (n : ι → ℤ) (E : ι → Fin 4 → α) (s : Fin 4 → ℤ) (h : α → G) :
    ∏ i ∈ T, (∏ j, h (E i j) ^ s j) ^ n i =
      ∏ e ∈ (T ×ˢ Finset.univ).image (fun p : ι × Fin 4 => E p.1 p.2),
        h e ^ (∑ i ∈ T, ∑ j, if E i j = e then n i * s j else 0) := by
  simp_rw [zpow_finset_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Finset.prod_zpow, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_eq_single (E i j)]
  · rw [if_pos rfl, ← zpow_mul, mul_comm]
  · intro e _ hne
    rw [if_neg (Ne.symm hne), zpow_zero]
  · intro hnot
    exact absurd (Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩,
      rfl⟩) hnot

end Regroup

/-! ## Integrality of `ω_det` on cycles -/

section Integrality

variable {Q : H →L[ℂ] H}

theorem edgeHol_ne_zero (hQ : IsStarProjection Q) (e : ℝ → SLSpace H) :
    edgeHol Q Pp e ≠ 0 := by
  classical
  unfold edgeHol
  split_ifs with h
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => segHol_ne_zero hQ ?_
    have : (0 : ℝ) ≤ (Nat.find h : ℝ) := Nat.cast_nonneg _
    gcongr; linarith
  · exact one_ne_zero

/-- `Q` is an admissible frame of itself. -/
theorem isAdmissibleFrame_self (hQ : IsStarProjection Q) : IsAdmissibleFrame Q Q Q := by
  have hQi := hQ.isIdempotentElem
  refine ⟨isFrameOf_of_inverse hQ.isSelfAdjoint hQi hQ.isSelfAdjoint hQi hQi.eq hQi.eq hQi.eq
    hQi.eq, by simpa using isHilbertSchmidt_zero, ⊥, inferInstance, fun x => ?_⟩
  simp [hQi.eq]

theorem GrSquare.edge_zero_mem (S : GrSquare Pp) (j : Fin 4) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, S.edge j 0 = S.map q := by
  fin_cases j
  · exact ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩, rfl⟩
  · exact ⟨(1, 0), ⟨⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩⟩, rfl⟩
  · exact ⟨(0, 1), ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩, rfl⟩
  · exact ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩, rfl⟩

/-- The square holonomy identity in edge form: `∏ⱼ hol(eⱼ)^{εⱼ} = exp ∫∫ Tr(P[∂ₛP, ∂ₜP])`. -/
theorem GrSquare.prod_edgeHol (hQ : IsStarProjection Q) (S : GrSquare Pp) (hS : S.InSector Q) :
    ∏ j : Fin 4, (Units.mk0 (edgeHol Q Pp (S.edge j)) (edgeHol_ne_zero hQ _)) ^ edgeSign j =
      Units.mk0 (Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareCurvature Pp S.map (x, y))) (Complex.exp_ne_zero _) := by
  have h := square_holonomy hQ S.smooth S.proj hS
  ext
  simp only [Fin.prod_univ_four, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, edgeSign,
    GrSquare.edge]
  have nt := edgeHol_ne_zero (Pp := Pp) hQ (hLine S.map 1)
  have nl := edgeHol_ne_zero (Pp := Pp) hQ (vLine S.map 0)
  simp only [zpow_one, zpow_neg]
  field_simp
  linear_combination h

/-- **Single-sector integrality**: for a sub-chain in one admissible sector whose boundary vanishes
on non-degenerate paths, `exp(2πi ∫ ω_det) = 1`. -/
theorem exp_kahlerOn_eq_one (hQ : IsStarProjection Q) (c : GrChain Pp) (T : Finset (Fin c.len))
    (hcyc : ∀ e, ¬ IsDegeneratePath e → c.bdryOn T e = 0)
    (hsec : ∀ k ∈ T, (c.sq k).InSector Q) :
    Complex.exp (2 * Real.pi * Complex.I * c.kahlerOn T) = 1 := by
  classical
  set hU : (ℝ → SLSpace H) → ℂˣ := fun e => Units.mk0 (edgeHol Q Pp e) (edgeHol_ne_zero hQ e)
  have hreg := prod_regroup T c.coeff (fun k j => (c.sq k).edge j) edgeSign hU
  -- every factor on the right is trivial
  have hright : ∏ e ∈ (T ×ˢ Finset.univ).image (fun p : Fin c.len × Fin 4 => (c.sq p.1).edge p.2),
      hU e ^ (∑ i ∈ T, ∑ j, if (c.sq i).edge j = e then c.coeff i * edgeSign j else 0) = 1 := by
    refine Finset.prod_eq_one fun e he => ?_
    obtain ⟨⟨k, j⟩, hkj, rfl⟩ := Finset.mem_image.mp he
    have hk : k ∈ T := (Finset.mem_product.mp hkj).1
    by_cases hdeg : IsDegeneratePath ((c.sq k).edge j)
    · obtain ⟨q, hq, hq0⟩ := (c.sq k).edge_zero_mem j
      obtain ⟨u, hu⟩ := hsec k hk q hq
      have h1 : edgeHol Q Pp ((c.sq k).edge j) = 1 :=
        edgeHol_const hQ hdeg (u₀ := u) (by rw [hq0]; exact hu)
      have : hU ((c.sq k).edge j) = 1 := Units.ext (by simp [hU, h1])
      rw [this, one_zpow]
    · have h0 := hcyc _ hdeg
      have : (∑ i ∈ T, ∑ j', if (c.sq i).edge j' = (c.sq k).edge j then
          c.coeff i * edgeSign j' else 0) = c.bdryOn T ((c.sq k).edge j) := by
        unfold GrChain.bdryOn; congr
      rw [this, h0, zpow_zero]
  -- every square factor is the exponential of its curvature integral
  have hleft : ∏ i ∈ T, (∏ j, hU ((c.sq i).edge j) ^ edgeSign j) ^ c.coeff i =
      ∏ i ∈ T, (Units.mk0 (Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareCurvature Pp (c.sq i).map (x, y))) (Complex.exp_ne_zero _)) ^ c.coeff i :=
    Finset.prod_congr rfl fun i hi => by rw [GrSquare.prod_edgeHol hQ _ (hsec i hi)]
  rw [hleft, hright] at hreg
  have hval := congrArg Units.val hreg
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one] at hval
  rw [← hval, GrChain.kahlerOn]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Complex.exp_int_mul, integral_squareCurvature_eq_kahler]
  ring_nf

theorem exists_int_of_exp_two_pi_I_mul_eq_one {x : ℝ}
    (h : Complex.exp (2 * Real.pi * Complex.I * x) = 1) : ∃ z : ℤ, x = z := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (x : ℂ) = n := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast this

/-- **Integrality of the determinant-line Kähler form on cycles** (sub-chain form): every
sub-chain whose boundary vanishes on non-degenerate paths has `∫ ω_det ∈ ℤ`. -/
theorem kahlerOn_mem_int (c : GrChain Pp) (T : Finset (Fin c.len))
    (hcyc : ∀ e, ¬ IsDegeneratePath e → c.bdryOn T e = 0) : ∃ z : ℤ, c.kahlerOn T = z := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with hT | ⟨k₀, hk₀⟩
    · exact ⟨0, by simp [GrChain.kahlerOn, hT]⟩
    set Q := Pp + ((c.sq k₀).map (0, 0)).op
    have hQ : IsStarProjection Q := (c.sq k₀).proj _
    set T₁ := T.filter fun k => (c.sq k).InSector Q
    set T₂ := T.filter fun k => ¬ (c.sq k).InSector Q
    have hk₀₁ : (c.sq k₀).InSector Q := (c.sq k₀).inSector_of_mem hQ
      ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩ ⟨Q, isAdmissibleFrame_self hQ⟩
    -- an edge of a sector square is not an edge of a non-sector square
    have hsep : ∀ k ∈ T₁, ∀ k' ∈ T₂, ∀ j j', (c.sq k).edge j ≠ (c.sq k').edge j' := by
      intro k hk k' hk' j j' heq
      have hk1 := (Finset.mem_filter.mp hk).2
      have hk2 := (Finset.mem_filter.mp hk').2
      obtain ⟨q, hq, hq0⟩ := (c.sq k).edge_zero_mem j
      obtain ⟨q', hq', hq0'⟩ := (c.sq k').edge_zero_mem j'
      obtain ⟨u, hu⟩ := hk1 q hq
      apply hk2
      refine (c.sq k').inSector_of_mem hQ hq' ⟨u, ?_⟩
      rw [← hq0', ← heq, hq0]; exact hu
    have hsplit : ∀ e, c.bdryOn T e = c.bdryOn T₁ e + c.bdryOn T₂ e := fun e => by
      unfold GrChain.bdryOn
      rw [Finset.sum_filter_add_sum_filter_not]
    have hzero : ∀ e, ¬ IsDegeneratePath e → c.bdryOn T₁ e = 0 ∧ c.bdryOn T₂ e = 0 := by
      intro e he
      have htot := hcyc e he
      by_cases hedge : ∃ k ∈ T₁, ∃ j, (c.sq k).edge j = e
      · obtain ⟨k, hk, j, rfl⟩ := hedge
        have h2 : c.bdryOn T₂ ((c.sq k).edge j) = 0 := by
          unfold GrChain.bdryOn
          refine Finset.sum_eq_zero fun k' hk' => Finset.sum_eq_zero fun j' _ => ?_
          rw [if_neg (Ne.symm (hsep k hk k' hk' j j'))]
        rw [hsplit, h2, add_zero] at htot
        exact ⟨htot, h2⟩
      · push Not at hedge
        have h1 : c.bdryOn T₁ e = 0 := by
          unfold GrChain.bdryOn
          refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg (hedge k hk j)]
        rw [hsplit, h1, zero_add] at htot
        exact ⟨h1, htot⟩
    -- the sector part is integral
    obtain ⟨z₁, hz₁⟩ := exists_int_of_exp_two_pi_I_mul_eq_one (exp_kahlerOn_eq_one hQ c T₁
      (fun e he => (hzero e he).1) fun k hk => (Finset.mem_filter.mp hk).2)
    -- the remainder has fewer squares
    have hlt : T₂ ⊂ T := by
      refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
      have := (Finset.mem_filter.mp (hsub hk₀)).2
      exact this hk₀₁
    obtain ⟨z₂, hz₂⟩ := ih T₂ hlt fun e he => (hzero e he).2
    refine ⟨z₁ + z₂, ?_⟩
    have hsum : c.kahlerOn T = c.kahlerOn T₁ + c.kahlerOn T₂ := by
      unfold GrChain.kahlerOn
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsum, hz₁, hz₂]; push_cast; ring

/-- **Integrality of the first Chern class of the determinant line**: the integral of `ω_det`
over every cycle of the restricted Grassmannian is an integer. -/
theorem GrChain.kahlerIntegral_mem_int (c : GrChain Pp) (hc : c.IsCycle) :
    ∃ z : ℤ, c.kahlerIntegral = z :=
  kahlerOn_mem_int c Finset.univ hc

end Integrality

end

end GaloisForLFunctions.HTGeometry
