import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.HTGeometry.RankThreeHankelMixture
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Five-point cusp from literal signed jet minors

Central finite differences separate the five sampled coordinates into the even orders 0, 2, 4
and odd orders 1, 3. Exact stencil moments and Taylor's theorem give an entrywise limit using
only eight derivatives. Strict positivity of both limiting jet blocks then opens a punctured
five-point positive-definite chamber. All finite-gap coordinates are connected by an exact
quadratic-form congruence.
-/

open Filter Topology Set Matrix
namespace HilbertMetric
noncomputable section

/-- A finite symmetric-sample stencil before division by its coalescence order. -/
def fiveSampleStencil (w : Fin 5 → ℝ) (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∑ k, w k * f ((k : ℝ) * h)

private theorem contDiff_fiveSampleStencil {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (w : Fin 5 → ℝ) :
    ContDiff ℝ n (fiveSampleStencil w f) := by
  unfold fiveSampleStencil
  fun_prop

private theorem iteratedDeriv_fiveSampleStencil_zero {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (w : Fin 5 → ℝ) :
    iteratedDeriv n (fiveSampleStencil w f) 0 =
      (∑ k, w k * (k : ℝ)^n) * iteratedDeriv n f 0 := by
  unfold fiveSampleStencil
  rw [iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field]
  simp_rw [iteratedDeriv_comp_const_mul hf]
  simp only [mul_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Taylor's theorem for a function with all lower jets zero. -/
theorem tendsto_div_pow_of_flat_jets {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f)
    (hflat : ∀ k : ℕ, k < n → iteratedDeriv k f 0 = 0) :
    Tendsto (fun h : ℝ => f h / h^n) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv n f 0 / (n.factorial : ℝ))) := by
  have hpoly (h : ℝ) : taylorWithinEval f n univ 0 h =
      (iteratedDeriv n f 0 / (n.factorial : ℝ)) * h^n := by
    rw [taylor_within_apply]
    simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
    rw [Finset.sum_eq_single n]
    · ring
    · intro k hk hkn
      rw [hflat k (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn)]
      ring
    · simp
  have htaylor := Real.taylor_tendsto (f:=f) (n:=n) convex_univ (mem_univ 0)
    hf.contDiffOn
  simp only [nhdsWithin_univ, sub_zero, hpoly] at htaylor
  have hlim' : Tendsto (fun h : ℝ =>
      iteratedDeriv n f 0 / (n.factorial : ℝ) +
        (f h - (iteratedDeriv n f 0 / (n.factorial : ℝ))*h^n)/h^n)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv n f 0 / (n.factorial : ℝ))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := iteratedDeriv n f 0 / (n.factorial : ℝ))).add
        (htaylor.mono_left (show (𝓝[≠] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  field_simp [hh0]
  ring

/-- Exact stencil moments identify the limiting literal derivative. -/
theorem tendsto_fiveSampleStencil_div_pow {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (w : Fin 5 → ℝ) (c : ℝ)
    (hflat : ∀ k : ℕ, k < n → (∑ i, w i * (i : ℝ)^k) * iteratedDeriv k f 0 = 0)
    (htop : (∑ i, w i * (i : ℝ)^n) = c * (n.factorial : ℝ)) :
    Tendsto (fun h : ℝ => fiveSampleStencil w f h / h^n) (𝓝[≠] 0)
      (𝓝 (c * iteratedDeriv n f 0)) := by
  have h := tendsto_div_pow_of_flat_jets (contDiff_fiveSampleStencil hf w) (by
    intro k hk
    rw [iteratedDeriv_fiveSampleStencil_zero (hf.of_le (by exact_mod_cast hk.le))]
    exact hflat k hk)
  rw [iteratedDeriv_fiveSampleStencil_zero hf, htop] at h
  convert h using 1
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp


/-- Signed jet matrix reached by five finite-difference coordinates. -/
def fivePointJetMatrix (j0 j2 j4 j6 j8 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![j0, 0, j2, 0, j4;
     0, -j2, 0, -j4, 0;
     j2, 0, j4, 0, j6;
     0, -j4, 0, -j6, 0;
     j4, 0, j6, 0, j8]

private theorem twoQuadratic_pos {a b c x y : ℝ}
    (ha : 0 < a) (hd : 0 < a*c-b^2) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a*x^2 + 2*b*x*y + c*y^2 := by
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := hxy.resolve_right (by simp)
    simpa using mul_pos ha (sq_pos_of_ne_zero hx)
  · have hid : a*(a*x^2+2*b*x*y+c*y^2) =
        (a*x+b*y)^2 + (a*c-b^2)*y^2 := by ring
    have hp : 0 < a*(a*x^2+2*b*x*y+c*y^2) := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hd (sq_pos_of_ne_zero hy))
    exact (mul_pos_iff_of_pos_left ha).mp hp

private theorem threeQuadratic_pos {a b c d e x y z : ℝ}
    (ha : 0 < a) (hd : 0 < a*c-b^2)
    (hD : 0 < signedEvenHankelThreeDet a b c d e)
    (hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < a*x^2+2*b*x*y+c*(y^2+2*x*z)+2*d*y*z+e*z^2 := by
  by_cases hz : z = 0
  · subst z
    have hxy : x ≠ 0 ∨ y ≠ 0 := by simpa using hxyz
    simpa using twoQuadratic_pos ha hd hxy
  · exact GaloisForLFunctions.HTGeometry.threeByThreeQuadratic_pos_of_minors ha hd hD hz

/-- The two strict jet blocks give the full five-dimensional limiting form. -/
theorem fivePointJetMatrix_posDef {j0 j2 j4 j6 j8 : ℝ}
    (h0 : 0 < j0) (h2 : j2 < 0)
    (h4 : 0 < j0*j4-j2^2) (h6 : 0 < j2*j6-j4^2)
    (h8 : 0 < signedEvenHankelThreeDet j0 j2 j4 j6 j8) :
    (fivePointJetMatrix j0 j2 j4 j6 j8).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fivePointJetMatrix]
  · intro v hv
    let E := j0*(v 0)^2+2*j2*v 0*v 2+j4*((v 2)^2+2*v 0*v 4)+
      2*j6*v 2*v 4+j8*(v 4)^2
    let O := -j2*(v 1)^2+2*(-j4)*v 1*v 3+(-j6)*(v 3)^2
    have hEp : (v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0) → 0 < E :=
      fun h => threeQuadratic_pos h0 h4 h8 h
    have hOp : (v 1 ≠ 0 ∨ v 3 ≠ 0) → 0 < O := by
      intro h
      apply twoQuadratic_pos (neg_pos.mpr h2) _ h
      nlinarith only [h6]
    have hEn : 0 ≤ E := by
      by_cases h : v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0
      · exact (hEp h).le
      · push Not at h
        simp [E, h.1, h.2.1, h.2.2]
    have hOn : 0 ≤ O := by
      by_cases h : v 1 ≠ 0 ∨ v 3 ≠ 0
      · exact (hOp h).le
      · push Not at h
        simp [O, h.1, h.2]
    have hpos : 0 < E+O := by
      by_cases h : v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 4 ≠ 0
      · exact add_pos_of_pos_of_nonneg (hEp h) hOn
      · have ho : v 1 ≠ 0 ∨ v 3 ≠ 0 := by
          by_contra hn
          push Not at h hn
          apply hv
          funext i
          fin_cases i <;> simp [h.1, h.2.1, h.2.2, hn.1, hn.2]
        exact add_pos_of_nonneg_of_pos hEn (hOp ho)
    have heq : star v ⬝ᵥ (fivePointJetMatrix j0 j2 j4 j6 j8).mulVec v = E+O := by
      simp [fivePointJetMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, E, O]
      ring
    rw [heq]
    exact hpos

/-- Central-difference normalization of the five-point Gram form. -/
def fivePointNormalizedMatrix (f : ℝ → ℝ) (h : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  let e2 := fiveSampleStencil ![-2,2,0,0,0] f h / h^2
  let e4 := fiveSampleStencil ![6,-8,2,0,0] f h / h^4
  let e6 := fiveSampleStencil ![-20,30,-12,2,0] f h / h^6
  let e8 := fiveSampleStencil ![70,-112,56,-16,2] f h / h^8
  let o2 := fiveSampleStencil ![1/2,0,-1/2,0,0] f h / h^2
  let o4 := fiveSampleStencil ![-1,1/2,1,-1/2,0] f h / h^4
  let o6 := fiveSampleStencil ![5/2,-2,-2,2,-1/2] f h / h^6
  !![f 0, 0, e2, 0, e4;
     0, o2, 0, o4, 0;
     e2, 0, e4, 0, e6;
     0, o4, 0, o6, 0;
     e4, 0, e6, 0, e8]

/-- Each normalized entry converges using only eight derivatives. -/
theorem tendsto_fivePointNormalizedMatrix {f : ℝ → ℝ}
    (hf : ContDiff ℝ 8 f)
    (h1 : iteratedDeriv 1 f 0 = 0) (h3 : iteratedDeriv 3 f 0 = 0)
    (h5 : iteratedDeriv 5 f 0 = 0) (h7 : iteratedDeriv 7 f 0 = 0)
    (i j : Fin 5) :
    Tendsto (fun h => fivePointNormalizedMatrix f h i j) (𝓝[≠] 0)
      (𝓝 (fivePointJetMatrix (f 0) (iteratedDeriv 2 f 0) (iteratedDeriv 4 f 0)
        (iteratedDeriv 6 f 0) (iteratedDeriv 8 f 0) i j)) := by
  have he2 : Tendsto (fun h => fiveSampleStencil ![-2,2,0,0,0] f h / h^2)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=2)
      (hf.of_le (by norm_num)) ![-2,2,0,0,0] (1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have he4 : Tendsto (fun h => fiveSampleStencil ![6,-8,2,0,0] f h / h^4)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 4 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=4)
      (hf.of_le (by norm_num)) ![6,-8,2,0,0] (1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have he6 : Tendsto (fun h => fiveSampleStencil ![-20,30,-12,2,0] f h / h^6)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 6 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=6)
      (hf.of_le (by norm_num)) ![-20,30,-12,2,0] (1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have he8 : Tendsto (fun h => fiveSampleStencil ![70,-112,56,-16,2] f h / h^8)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 8 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=8)
      (hf.of_le (by norm_num)) ![70,-112,56,-16,2] (1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have ho2 : Tendsto (fun h => fiveSampleStencil ![1/2,0,-1/2,0,0] f h / h^2)
      (𝓝[≠] 0) (𝓝 (-iteratedDeriv 2 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=2)
      (hf.of_le (by norm_num)) ![1/2,0,-1/2,0,0] (-1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have ho4 : Tendsto (fun h => fiveSampleStencil ![-1,1/2,1,-1/2,0] f h / h^4)
      (𝓝[≠] 0) (𝓝 (-iteratedDeriv 4 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=4)
      (hf.of_le (by norm_num)) ![-1,1/2,1,-1/2,0] (-1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  have ho6 : Tendsto (fun h => fiveSampleStencil ![5/2,-2,-2,2,-1/2] f h / h^6)
      (𝓝[≠] 0) (𝓝 (-iteratedDeriv 6 f 0)) := by
    have hh := tendsto_fiveSampleStencil_div_pow (n:=6)
      (hf.of_le (by norm_num)) ![5/2,-2,-2,2,-1/2] (-1) (by
        intro k hk
        interval_cases k <;>
          norm_num [Fin.sum_univ_succ, h1, h3, h5, h7]) (by
        norm_num [Fin.sum_univ_succ, Nat.factorial])
    simpa using hh
  fin_cases i <;> fin_cases j <;>
    dsimp only [fivePointNormalizedMatrix, fivePointJetMatrix]
  all_goals first
    | exact he2
    | exact he4
    | exact he6
    | exact he8
    | exact ho2
    | exact ho4
    | exact ho6
    | exact tendsto_const_nhds

/-- Literal five-node Toeplitz Gram matrix. -/
def fivePointSampleMatrix (f : ℝ → ℝ) (h : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![f 0, f h, f (2*h), f (3*h), f (4*h);
     f h, f 0, f h, f (2*h), f (3*h);
     f (2*h), f h, f 0, f h, f (2*h);
     f (3*h), f (2*h), f h, f 0, f h;
     f (4*h), f (3*h), f (2*h), f h, f 0]

/-- Coordinates in the normalized central-difference basis. -/
def fivePointDifferenceCoordinates (h : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![v 0+v 1+v 2+v 3+v 4,
    h*(v 3-v 1+2*(v 4-v 0)),
    h^2/2*(v 1+v 3+4*v 0+4*v 4),
    h^3*(v 4-v 0),
    h^4/2*(v 0+v 4)]

private theorem fivePointDifferenceCoordinates_ne_zero {h : ℝ} (hh : h ≠ 0)
    {v : Fin 5 → ℝ} (hv : v ≠ 0) : fivePointDifferenceCoordinates h v ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  have h3 := congrFun hz 3
  have h4 := congrFun hz 4
  change v 0+v 1+v 2+v 3+v 4 = 0 at h0
  change h*(v 3-v 1+2*(v 4-v 0)) = 0 at h1
  change h^2/2*(v 1+v 3+4*v 0+4*v 4) = 0 at h2
  change h^3*(v 4-v 0) = 0 at h3
  change h^4/2*(v 0+v 4) = 0 at h4
  have h30 : v 4-v 0 = 0 := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 3 hh)
  have h40 : v 0+v 4 = 0 := (mul_eq_zero.mp h4).resolve_left
    (div_ne_zero (pow_ne_zero 4 hh) (by norm_num))
  have h20 : v 1+v 3+4*v 0+4*v 4 = 0 := (mul_eq_zero.mp h2).resolve_left
    (div_ne_zero (pow_ne_zero 2 hh) (by norm_num))
  have h10 : v 3-v 1+2*(v 4-v 0) = 0 := (mul_eq_zero.mp h1).resolve_left hh
  have hv0 : v 0 = 0 := by linarith only [h30, h40]
  have hv4 : v 4 = 0 := by linarith only [h30, h40]
  have hv1 : v 1 = 0 := by linarith only [h20, h10, hv0, hv4]
  have hv3 : v 3 = 0 := by linarith only [h20, h10, hv0, hv4]
  have hv2 : v 2 = 0 := by linarith only [h0, hv0, hv1, hv3, hv4]
  apply hv
  funext i
  fin_cases i <;> simp [hv0, hv1, hv2, hv3, hv4]

/-- Exact congruence, with every coalescence scale retained. -/
theorem fivePointSampleMatrix_quadratic_eq_normalized {h : ℝ} (hh : h ≠ 0)
    (f : ℝ → ℝ) (v : Fin 5 → ℝ) :
    star v ⬝ᵥ (fivePointSampleMatrix f h).mulVec v =
      star (fivePointDifferenceCoordinates h v) ⬝ᵥ
        (fivePointNormalizedMatrix f h).mulVec (fivePointDifferenceCoordinates h v) := by
  simp [fivePointSampleMatrix, fivePointNormalizedMatrix, fivePointDifferenceCoordinates,
    fiveSampleStencil, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  field_simp [hh]
  ring

/-- Positive normalized finite-difference form gives positive literal sample form. -/
theorem fivePointSampleMatrix_posDef_of_normalized {f : ℝ → ℝ} {h : ℝ}
    (hh : h ≠ 0) (hM : (fivePointNormalizedMatrix f h).PosDef) :
    (fivePointSampleMatrix f h).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fivePointSampleMatrix]
  · intro v hv
    rw [fivePointSampleMatrix_quadratic_eq_normalized hh]
    exact hM.dotProduct_mulVec_pos (fivePointDifferenceCoordinates_ne_zero hh hv)

/-- Strict signed jet minors open the five-point cusp using only `C^8` regularity. -/
theorem eventually_fivePointSampleMatrix_posDef {f : ℝ → ℝ}
    (hf : ContDiff ℝ 8 f)
    (h1 : iteratedDeriv 1 f 0 = 0) (h3 : iteratedDeriv 3 f 0 = 0)
    (h5 : iteratedDeriv 5 f 0 = 0) (h7 : iteratedDeriv 7 f 0 = 0)
    (h0 : 0 < f 0) (h2 : iteratedDeriv 2 f 0 < 0)
    (h4 : 0 < f 0*iteratedDeriv 4 f 0-(iteratedDeriv 2 f 0)^2)
    (h6 : 0 < iteratedDeriv 2 f 0*iteratedDeriv 6 f 0-(iteratedDeriv 4 f 0)^2)
    (h8 : 0 < signedEvenHankelThreeDet (f 0) (iteratedDeriv 2 f 0)
      (iteratedDeriv 4 f 0) (iteratedDeriv 6 f 0) (iteratedDeriv 8 f 0)) :
    ∀ᶠ h in 𝓝[≠] 0, (fivePointSampleMatrix f h).PosDef := by
  have hHerm : ∀ h : ℝ, (fivePointNormalizedMatrix f h).IsHermitian := by
    intro h
    rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fivePointNormalizedMatrix]
  have hM := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto
    (fivePointJetMatrix_posDef h0 h2 h4 h6 h8)
    (Filter.Eventually.of_forall hHerm)
    (tendsto_fivePointNormalizedMatrix hf h1 h3 h5 h7)
  filter_upwards [hM, self_mem_nhdsWithin] with h hh hn
  apply fivePointSampleMatrix_posDef_of_normalized _ hh
  simpa using hn

end
end HilbertMetric
