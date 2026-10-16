import GaloisForLFunctions.RHTower.CHMDThetaRelativeGraph

/-!
# Exact finite-divisor sources inside the CHMD compact-test completion

Every admissible finite Xi-divisor quotient, with a polynomial numerator of degree
at most the divisor-list length, is the complex source of two actual real graph
vectors. Both vectors are graph limits of genuine compact smooth tests. Their
literal source transform satisfies the exact divisor identity.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

/-- Undo the Doob gauge on a real and imaginary pair of graph vectors. -/
def complexSource (p q : SourceGraph) (x : ℝ) : ℂ :=
  (riemannKernelReal x : ℂ) * ((p.val.fst x : ℂ) + Complex.I * (q.val.fst x : ℂ))

theorem complexSource_of_relative_ae {u : ℝ → ℂ} {p q : SourceGraph}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).re))
    (hq : q.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).im)) :
    complexSource p q =ᵐ[volume] u := by
  apply volume_absolutelyContinuous_mass.ae_eq
  filter_upwards [hp, hq] with x hx hy
  dsimp only [complexSource]
  rw [hx, hy]
  dsimp only [phiDoobInv]
  have hk : (riemannKernelReal x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (riemannKernelReal_pos x).ne'
  rw [Complex.ofReal_div, Complex.ofReal_div]
  calc
    _ = ((u x).re : ℂ) + (u x).im * Complex.I := by field_simp
    _ = u x := Complex.re_add_im _

theorem sourceTransform_congr_ae {u v : ℝ → ℂ} (h : u =ᵐ[volume] v) (z : ℂ) :
    sourceTransform u z = sourceTransform v z := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Theta domination and global Lipschitz regularity suffice for full graph realization. -/
theorem exists_complex_relative_graph {u : ℝ → ℂ}
    (hl : ∃ C, LipschitzWith C u)
    (hb : ∃ M, ∀ x, ‖u x‖ ≤ M * thetaCuspFullSource x) :
    ∃ p q : SourceGraph,
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      p.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).re) ∧
      q.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (u x).im) ∧
      complexSource p q =ᵐ[volume] u := by
  obtain ⟨C, hC⟩ := hl
  obtain ⟨M, hM⟩ := hb
  simp_rw [thetaCuspFullSource_eq_riemannKernelReal] at hM
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((norm_nonneg (u 0)).trans (hM 0)) (riemannKernelReal_pos 0)
  have hre : LipschitzWith (1 * C) (fun x => (u x).re) := RCLike.lipschitzWith_re.comp hC
  have him : LipschitzWith (1 * C) (fun x => (u x).im) := RCLike.lipschitzWith_im.comp hC
  have hbr (x : ℝ) : |(u x).re| ≤ M * riemannKernelReal x :=
    (Complex.abs_re_le_norm _).trans (hM x)
  have hbi (x : ℝ) : |(u x).im| ≤ M * riemannKernelReal x :=
    (Complex.abs_im_le_norm _).trans (hM x)
  let p := relativeLift (fun x => (u x).re) hre hM0 hbr
  let q := relativeLift (fun x => (u x).im) him hM0 hbi
  have hp := relativeLift_source_ae (fun x => (u x).re) hre hM0 hbr
  have hq := relativeLift_source_ae (fun x => (u x).im) him hM0 hbi
  exact ⟨p, q, relativeLift_compact_approx _ hre hM0 hbr,
    relativeLift_compact_approx _ him hM0 hbi, hp, hq, complexSource_of_relative_ae hp hq⟩

/-- Finite divisor quotients have actual graph representatives, with no domain premise. -/
theorem finite_divisor_graph_realization {L : List ℂ} (hL : ThetaDivisionList L)
    (e : Polynomial ℂ) (he : e.natDegree ≤ L.length) :
    ∃ p q : SourceGraph,
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      p.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (listComb thetaListDivision L e x).re) ∧
      q.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (listComb thetaListDivision L e x).im) ∧
      complexSource p q =ᵐ[volume] listComb thetaListDivision L e ∧
      ∀ z, sourceTransform (complexSource p q) z * listDivisor L z = XiC z * e.eval (z ^ 2) := by
  obtain ⟨_, _, hb, hT, _⟩ := listComb_spec hL e he
  obtain ⟨p, q, hp, hq, hpr, hqi, hsource⟩ :=
    exists_complex_relative_graph (exists_lipschitz_listComb L e) hb
  refine ⟨p, q, hp, hq, hpr, hqi, hsource, fun z => ?_⟩
  rw [sourceTransform_congr_ae hsource]
  exact hT z

/-- An unconditional nonzero instance: a genuine real Xi zero can be divided out
inside the complete CHMD graph, with the full original Fourier mass retained. -/
theorem exists_exact_zero_division_graph :
    ∃ (γ : ℝ) (p q : SourceGraph), 0 < γ ∧ XiC (γ : ℂ) = 0 ∧
      p ∈ closure (compactTests : Set SourceGraph) ∧
      q ∈ closure (compactTests : Set SourceGraph) ∧
      complexSource p q =ᵐ[volume] zeroDivision (γ : ℂ) thetaSourceC ∧
      sourceTransform (complexSource p q) 0 = XiC 0 ∧
      sourceTransform (complexSource p q) 0 ≠ 0 ∧
      ∀ z, ((γ : ℂ) ^ 2 - z ^ 2) * sourceTransform (complexSource p q) z =
        (γ : ℂ) ^ 2 * XiC z := by
  obtain ⟨γ, hγ, hzero, _, _⟩ := exists_positive_thetaZeroDivision
  obtain ⟨p, q, hp, hq, _, _, hsource⟩ := exists_complex_relative_graph
    (exists_lipschitz_thetaListDivision [(γ : ℂ)])
    (exists_norm_thetaListDivision_le [(γ : ℂ)])
  have hT (z : ℂ) : ((γ : ℂ) ^ 2 - z ^ 2) * sourceTransform (complexSource p q) z =
      (γ : ℂ) ^ 2 * XiC z := by
    rw [sourceTransform_congr_ae hsource]
    simpa only [thetaListDivision, sourceTransform_thetaSourceC, hzero, sub_zero] using
      expMomentSource_thetaSourceC.sourceTransform_zeroDivision thetaSourceC_neg (γ : ℂ) z
  have hγ0 : (γ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hγ.ne')
  have hmass : sourceTransform (complexSource p q) 0 = XiC 0 := by
    have hz : (γ : ℂ) ^ 2 * (sourceTransform (complexSource p q) 0 - XiC 0) = 0 := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_sub] using
        sub_eq_zero.mpr (hT 0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hγ0)
  exact ⟨γ, p, q, hγ, hzero, hp, hq, hsource, hmass, hmass ▸ XiC_zero_ne, hT⟩

end RHTower.CHMDDoobGraph
