import GaloisForLFunctions.HTGeometry.DeterminantLineChainIntegrality

/-!
# Fillings and the relative deck integer of the determinant line

* `exp_kahlerOn_eq_prod`: within one admissible sector, `exp(2πi ∫ ω_det)` over a sub-chain is the
  product of the edge holonomies raised to the boundary multiplicities.
* `edgeHol_eq_exp_kahlerIntegral` (**holonomy–curvature**): if a chain `c` fills a non-degenerate
  path `γ` (its boundary is `γ` up to degenerate paths), then `hol(γ) = exp(2πi ∫_c ω_det)`; the
  squares outside the sector of `γ` form a cycle and contribute an integer.
* `GrChain.deck_integer`, `GrChain.fillings_same_holonomy`: two fillings of one boundary have the
  same holonomy, and `∫_{c₀} ω_det − ∫_{c₁} ω_det = ⟨c₁(L_det), c₀ − c₁⟩ ∈ ℤ`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Pp Q : H →L[ℂ] H}

/-! ## The sector product formula -/

open Classical in
/-- Within one admissible sector, `exp(2πi ∫ ω_det)` over a sub-chain is the product of the edge
holonomies raised to the boundary multiplicities. -/
theorem exp_kahlerOn_eq_prod (hQ : IsStarProjection Q) (c : GrChain Pp) (T : Finset (Fin c.len))
    (hsec : ∀ k ∈ T, (c.sq k).InSector Q) :
    Complex.exp (2 * Real.pi * Complex.I * c.kahlerOn T) =
      ∏ e ∈ (T ×ˢ Finset.univ).image (fun p : Fin c.len × Fin 4 => (c.sq p.1).edge p.2),
        edgeHol Q Pp e ^ c.bdryOn T e := by
  classical
  set hU : (ℝ → SLSpace H) → ℂˣ := fun e => Units.mk0 (edgeHol Q Pp e) (edgeHol_ne_zero hQ e)
  have hreg := prod_regroup T c.coeff (fun k j => (c.sq k).edge j) edgeSign hU
  have hleft : ∏ i ∈ T, (∏ j, hU ((c.sq i).edge j) ^ edgeSign j) ^ c.coeff i =
      ∏ i ∈ T, (Units.mk0 (Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareCurvature Pp (c.sq i).map (x, y))) (Complex.exp_ne_zero _)) ^ c.coeff i :=
    Finset.prod_congr rfl fun i hi => by rw [GrSquare.prod_edgeHol hQ _ (hsec i hi)]
  rw [hleft] at hreg
  have hval := congrArg Units.val hreg
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0] at hval
  have hexp : Complex.exp (2 * Real.pi * Complex.I * c.kahlerOn T) =
      ∏ i ∈ T, Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        squareCurvature Pp (c.sq i).map (x, y)) ^ c.coeff i := by
    rw [GrChain.kahlerOn]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Complex.exp_int_mul, integral_squareCurvature_eq_kahler]
    ring_nf
  rw [hexp, hval]
  refine Finset.prod_congr rfl fun e _ => ?_
  unfold GrChain.bdryOn
  congr

/-! ## Fillings of loops -/

open Classical in
/-- A chain fills the path `γ`: its boundary is `γ` up to degenerate paths. -/
def GrChain.Fills (c : GrChain Pp) (γ : ℝ → SLSpace H) : Prop :=
  ∀ e, ¬ IsDegeneratePath e → c.bdry e = if e = γ then 1 else 0

/-- **Holonomy–curvature theorem.**  If a chain fills the non-degenerate path `γ` and `γ(0)` lies in
the admissible sector of `Q`, then `hol_Q(γ) = exp(2πi ∫_c ω_det)`. -/
theorem edgeHol_eq_exp_kahlerIntegral (hQ : IsStarProjection Q) (c : GrChain Pp)
    {γ : ℝ → SLSpace H} (hγ : ¬ IsDegeneratePath γ) (hc : c.Fills γ)
    (hγsec : ∃ u, IsAdmissibleFrame Q u (Pp + (γ 0).op)) :
    edgeHol Q Pp γ = Complex.exp (2 * Real.pi * Complex.I * c.kahlerIntegral) := by
  classical
  set T₁ := Finset.univ.filter fun k => (c.sq k).InSector Q
  set T₂ := Finset.univ.filter fun k => ¬ (c.sq k).InSector Q
  have hsep : ∀ k ∈ T₁, ∀ k' ∈ T₂, ∀ j j', (c.sq k).edge j ≠ (c.sq k').edge j' := by
    intro k hk k' hk' j j' heq
    obtain ⟨q, hq, hq0⟩ := (c.sq k).edge_zero_mem j
    obtain ⟨q', hq', hq0'⟩ := (c.sq k').edge_zero_mem j'
    obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hk).2 q hq
    apply (Finset.mem_filter.mp hk').2
    refine (c.sq k').inSector_of_mem hQ hq' ⟨u, ?_⟩
    rw [← hq0', ← heq, hq0]; exact hu
  have hsplit : ∀ e, c.bdry e = c.bdryOn T₁ e + c.bdryOn T₂ e := fun e => by
    unfold GrChain.bdry GrChain.bdryOn
    rw [Finset.sum_filter_add_sum_filter_not]
  -- `γ` is an edge of a sector square
  have hγedge : ∃ k ∈ T₁, ∃ j, (c.sq k).edge j = γ := by
    have h1 := hc γ hγ
    rw [if_pos rfl] at h1
    by_contra hnone
    push Not at hnone
    have : c.bdry γ = 0 := by
      unfold GrChain.bdry GrChain.bdryOn
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro heq
      obtain ⟨q, hq, hq0⟩ := (c.sq k).edge_zero_mem j
      obtain ⟨u, hu⟩ := hγsec
      have hin : (c.sq k).InSector Q :=
        (c.sq k).inSector_of_mem hQ hq ⟨u, by rw [← hq0, heq]; exact hu⟩
      exact hnone k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩) j heq
    rw [this] at h1; exact zero_ne_one h1
  obtain ⟨k₀, hk₀, j₀, hj₀⟩ := hγedge
  -- the boundary splits along the two parts
  have hparts : ∀ e, ¬ IsDegeneratePath e →
      c.bdryOn T₁ e = (if e = γ then 1 else 0) ∧ c.bdryOn T₂ e = 0 := by
    intro e he
    have htot := hc e he
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
      have hne : e ≠ γ := fun h => hedge k₀ hk₀ j₀ (hj₀.trans h.symm)
      rw [hsplit, h1, zero_add, if_neg hne] at htot
      exact ⟨by rw [h1, if_neg hne], htot⟩
  -- the non-sector part is a cycle, hence integral
  obtain ⟨z₂, hz₂⟩ := kahlerOn_mem_int c T₂ fun e he => (hparts e he).2
  -- the sector part has holonomy `hol(γ)`
  have hprod := exp_kahlerOn_eq_prod hQ c T₁ fun k hk => (Finset.mem_filter.mp hk).2
  have hγmem : γ ∈ (T₁ ×ˢ Finset.univ).image
      (fun p : Fin c.len × Fin 4 => (c.sq p.1).edge p.2) :=
    Finset.mem_image.mpr ⟨(k₀, j₀), Finset.mem_product.mpr ⟨hk₀, Finset.mem_univ _⟩, hj₀⟩
  rw [Finset.prod_eq_single γ (fun e he hne => ?_) (fun h => absurd hγmem h),
    (hparts γ hγ).1, if_pos rfl, zpow_one] at hprod
  · have hsum : c.kahlerIntegral = c.kahlerOn T₁ + c.kahlerOn T₂ := by
      unfold GrChain.kahlerIntegral GrChain.kahlerOn
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsum, hz₂, ← hprod]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z₂ : ℂ)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨z₂, by ring⟩
    rw [this, mul_one]
  · by_cases hdeg : IsDegeneratePath e
    · obtain ⟨⟨k, j⟩, hkj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨q, hq, hq0⟩ := (c.sq k).edge_zero_mem j
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp (Finset.mem_product.mp hkj).1).2 q hq
      rw [edgeHol_const hQ hdeg (u₀ := u) (by rw [hq0]; exact hu), one_zpow]
    · rw [(hparts e hdeg).1, if_neg hne, zpow_zero]

/-! ## Sums and differences of chains -/

/-- The sum of two chains. -/
def GrChain.add (c c' : GrChain Pp) : GrChain Pp where
  len := c.len + c'.len
  coeff := Fin.append c.coeff c'.coeff
  sq := Fin.append c.sq c'.sq

/-- The negative of a chain. -/
def GrChain.neg (c : GrChain Pp) : GrChain Pp where
  len := c.len
  coeff := fun k => -c.coeff k
  sq := c.sq

theorem GrChain.bdry_add (c c' : GrChain Pp) (e : ℝ → SLSpace H) :
    (c.add c').bdry e = c.bdry e + c'.bdry e := by
  unfold GrChain.bdry GrChain.bdryOn
  change ∑ k : Fin (c.len + c'.len), _ = _
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  · have h1 : (c.add c').sq (Fin.castAdd c'.len k) = c.sq k := Fin.append_left _ _ _
    have h2 : (c.add c').coeff (Fin.castAdd c'.len k) = c.coeff k := Fin.append_left _ _ _
    rw [h2]; split_ifs with ha hb hb <;> first | rfl | (rw [h1] at ha; contradiction)
  · have h1 : (c.add c').sq (Fin.natAdd c.len k) = c'.sq k := Fin.append_right _ _ _
    have h2 : (c.add c').coeff (Fin.natAdd c.len k) = c'.coeff k := Fin.append_right _ _ _
    rw [h2]; split_ifs with ha hb hb <;> first | rfl | (rw [h1] at ha; contradiction)

theorem GrChain.bdry_neg (c : GrChain Pp) (e : ℝ → SLSpace H) : c.neg.bdry e = -c.bdry e := by
  simp only [GrChain.bdry, GrChain.bdryOn, GrChain.neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem GrChain.kahlerIntegral_add (c c' : GrChain Pp) :
    (c.add c').kahlerIntegral = c.kahlerIntegral + c'.kahlerIntegral := by
  unfold GrChain.kahlerIntegral GrChain.kahlerOn
  change ∑ k : Fin (c.len + c'.len), _ = _
  rw [Fin.sum_univ_add]
  simp [GrChain.add]

theorem GrChain.kahlerIntegral_neg (c : GrChain Pp) :
    c.neg.kahlerIntegral = -c.kahlerIntegral := by
  unfold GrChain.kahlerIntegral GrChain.kahlerOn
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [GrChain.neg]
  push_cast; ring

/-! ## Two fillings of one boundary -/

/-- **The relative deck integer.**  Two chains filling the same non-degenerate path have
`∫_{c₀} ω_det − ∫_{c₁} ω_det ∈ ℤ`; this integer is `⟨c₁(L_det), c₀ − c₁⟩`. -/
theorem GrChain.deck_integer (c₀ c₁ : GrChain Pp) {γ : ℝ → SLSpace H} (h₀ : c₀.Fills γ)
    (h₁ : c₁.Fills γ) : ∃ q : ℤ, c₀.kahlerIntegral - c₁.kahlerIntegral = q := by
  have hcyc : (c₀.add c₁.neg).IsCycle := fun e he => by
    rw [GrChain.bdry_add, GrChain.bdry_neg, h₀ e he, h₁ e he, add_neg_cancel]
  obtain ⟨q, hq⟩ := (c₀.add c₁.neg).kahlerIntegral_mem_int hcyc
  refine ⟨q, ?_⟩
  rw [← hq, GrChain.kahlerIntegral_add, GrChain.kahlerIntegral_neg, sub_eq_add_neg]

/-- **Two fillings have the same determinant holonomy**: both equal the holonomy of the boundary
path, and they differ by the deck translation `q`. -/
theorem GrChain.fillings_same_holonomy (hQ : IsStarProjection Q) (c₀ c₁ : GrChain Pp)
    {γ : ℝ → SLSpace H} (hγ : ¬ IsDegeneratePath γ) (h₀ : c₀.Fills γ) (h₁ : c₁.Fills γ)
    (hγsec : ∃ u, IsAdmissibleFrame Q u (Pp + (γ 0).op)) :
    Complex.exp (2 * Real.pi * Complex.I * c₀.kahlerIntegral) = edgeHol Q Pp γ ∧
      Complex.exp (2 * Real.pi * Complex.I * c₁.kahlerIntegral) = edgeHol Q Pp γ :=
  ⟨(edgeHol_eq_exp_kahlerIntegral hQ c₀ hγ h₀ hγsec).symm,
    (edgeHol_eq_exp_kahlerIntegral hQ c₁ hγ h₁ hγsec).symm⟩

end

end GaloisForLFunctions.HTGeometry
