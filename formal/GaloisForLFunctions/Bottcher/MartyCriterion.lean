/-
# Marty's criterion — normality from bounded spherical derivative

The qualitative Marty criterion: a sequence of functions holomorphic on `ball c R` with **uniformly
bounded spherical derivative** (`σ(f_n) ≤ M`) is a **normal family** — its lift `stereo ∘ f_n` into the
compact unit sphere `S² ⊂ ℝ³` has a subsequence converging uniformly on compact subsets. This is the
normality engine of the Fatou/Julia dichotomy and the gateway to the three-value test.

The proof: `stereo` lands in the unit sphere (`norm_stereo_eq_one`, a compact target) and is continuous
(`continuous_stereo`); the lifted family is equicontinuous by the quantitative Marty bound
(`marty_equicontinuity`, giving `‖stereo(f_n a) - stereo(f_n b)‖ = 2χ ≤ 2M‖a-b‖`). Arzelà–Ascoli
(`BoundedContinuousFunction.arzela_ascoli`) then yields the convergent subsequence — the same engine as
`montel_subseq`, now in the chordal metric.

New file (Montel/Julia lane — Marty's criterion). Consumes `Marty`.
-/
import GaloisForLFunctions.Bottcher.Marty
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open Complex Metric Set Filter Topology BoundedContinuousFunction

namespace Bottcher

theorem norm_stereo_eq_one (z : ℂ) : ‖stereo z‖ = 1 := by
  rw [stereo, norm_euclidean3, Real.sqrt_eq_one]
  have hzn : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hzn]
  have hd : (1:ℝ) + (z.re^(2 : ℕ) + z.im^(2 : ℕ)) ≠ 0 :=
    (show (0:ℝ) < 1 + (z.re^(2 : ℕ)+z.im^(2 : ℕ)) by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]).ne'
  field_simp; ring

theorem continuous_stereo : Continuous stereo := by
  have hden : ∀ z : ℂ, (1 : ℝ) + ‖z‖ ^ (2 : ℕ) ≠ 0 := fun z => (by positivity : (0:ℝ) < 1 + ‖z‖^(2 : ℕ)).ne'
  have hc : Continuous (fun z : ℂ => (1 : ℝ) + ‖z‖ ^ (2 : ℕ)) := by fun_prop
  have hpi : Continuous (fun z : ℂ =>
      (![2*z.re/(1+‖z‖^(2 : ℕ)), 2*z.im/(1+‖z‖^(2 : ℕ)), (‖z‖^(2 : ℕ)-1)/(1+‖z‖^(2 : ℕ))] : Fin 3 → ℝ)) := by
    apply continuous_pi; intro i; fin_cases i
    · exact Continuous.div (by fun_prop) hc hden
    · exact Continuous.div (by fun_prop) hc hden
    · exact Continuous.div (by fun_prop) hc hden
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hpi

/-- **Marty's criterion (normal subsequence).** A sequence of functions holomorphic on `ball c R` with
uniformly bounded spherical derivative `≤ M` is **normal**: the lifted family `stereo ∘ f_n` (into the
compact unit sphere) has a subsequence converging uniformly on `closedBall c r` (`r < R`). The chordal
normality at the heart of the Fatou/Julia dichotomy and the three-value test. -/
theorem marty_normal_subseq {f : ℕ → ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hr0 : 0 < r) (hrR : r < R)
    (hf : ∀ n, ∀ z ∈ ball c R, DifferentiableAt ℂ (f n) z)
    (hM : ∀ n, ∀ z ∈ ball c R, sphericalDeriv (f n) z ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
      TendstoUniformlyOn (fun k => fun z => stereo (f (φ k) z)) g atTop (closedBall c r) := by
  classical
  haveI hcs : CompactSpace ↥(closedBall c r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hsubR : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hM0 : 0 ≤ M := le_trans (sphericalDeriv_nonneg (f 0) c) (hM 0 c (mem_ball_self (by linarith)))
  -- lifted family continuous on the closed ball
  have hcont : ∀ n, ContinuousOn (fun z => stereo (f n z)) (closedBall c r) := fun n =>
    continuous_stereo.comp_continuousOn (fun z hz => (hf n z (hsubR hz)).continuousAt.continuousWithinAt)
  let cmap : ℕ → C(↥(closedBall c r), EuclideanSpace ℝ (Fin 3)) :=
    fun n => ⟨(closedBall c r).restrict (fun z => stereo (f n z)), (hcont n).restrict⟩
  let bcfF : ℕ → ↥(closedBall c r) →ᵇ EuclideanSpace ℝ (Fin 3) := fun n => mkOfCompact (cmap n)
  have hval : ∀ n (x : ↥(closedBall c r)), bcfF n x = stereo (f n (x : ℂ)) := fun n x => rfl
  set A : Set (↥(closedBall c r) →ᵇ EuclideanSpace ℝ (Fin 3)) := Set.range bcfF with hA
  have hsec : ∀ a : ↥A, bcfF ((a.2).choose) = (a : ↥(closedBall c r) →ᵇ EuclideanSpace ℝ (Fin 3)) :=
    fun a => (a.2).choose_spec
  -- equicontinuity from Marty
  have hH : Equicontinuous ((↑) : ↥A → ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun d => 2 * M * d)
    · have : Continuous (fun d : ℝ => 2 * M * d) := by fun_prop
      simpa using this.tendsto 0
    · intro x y a
      obtain ⟨n, hn⟩ := a.2
      have hax : (↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) x = stereo (f n (x : ℂ)) :=
        (DFunLike.congr_fun hn.symm x).trans (hval n x)
      have hay : (↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) y = stereo (f n (y : ℂ)) :=
        (DFunLike.congr_fun hn.symm y).trans (hval n y)
      have hmarty := marty_equicontinuity (convex_ball c R) (hf n) (hM n) (hsubR x.2) (hsubR y.2)
      have hLHS : dist ((↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) x)
          ((↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) y)
          = 2 * chordalDist (f n (x : ℂ)) (f n (y : ℂ)) := by
        rw [hax, hay, dist_eq_norm, norm_stereo_sub]
      have hRHS : (2 : ℝ) * M * dist x y = 2 * M * ‖(x : ℂ) - (y : ℂ)‖ := by
        rw [Subtype.dist_eq, Complex.dist_eq]
      show dist ((↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) x)
        ((↑a : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) y) ≤ 2 * M * dist x y
      rw [hLHS, hRHS]
      nlinarith [hmarty]
  have hin : ∀ (F : ↥(closedBall c r) →ᵇ EuclideanSpace ℝ (Fin 3)) (x : ↥(closedBall c r)),
      F ∈ A → F x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro F x hF
    obtain ⟨n, rfl⟩ := hF
    rw [mem_closedBall, dist_zero_right, hval n x, norm_stereo_eq_one]
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (isCompact_closedBall _ _) A hin hH
  have hmem : ∀ n, bcfF n ∈ closure A := fun n => subset_closure (mem_range_self n)
  obtain ⟨g, -, φ, hφmono, hφtends⟩ := hcompact.tendsto_subseq hmem
  have hunif := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp hφtends
  simp only [Function.comp_apply] at hunif
  let G : ℂ → EuclideanSpace ℝ (Fin 3) := fun z => if h : z ∈ closedBall c r then g ⟨z, h⟩ else 0
  have hGcoe : (G ∘ ((↑) : ↥(closedBall c r) → ℂ)) = (g : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)) := by
    funext x
    show (if h : (x : ℂ) ∈ closedBall c r then g ⟨(x : ℂ), h⟩ else 0) = g x
    rw [dif_pos x.2]
  have hfameq : (fun k => ((bcfF (φ k)) : ↥(closedBall c r) → EuclideanSpace ℝ (Fin 3)))
      = (fun k (x : ↥(closedBall c r)) => stereo (f (φ k) (x : ℂ))) := by
    funext k x; exact hval (φ k) x
  rw [hfameq, ← hGcoe] at hunif
  exact ⟨φ, G, hφmono, (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mpr hunif⟩

end Bottcher
