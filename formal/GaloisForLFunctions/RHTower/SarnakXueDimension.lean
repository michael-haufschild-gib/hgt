import GaloisForLFunctions.RHTower.SarnakXueCuspRegion
import GaloisForLFunctions.RHTower.SarnakXuePointwise
import GaloisForLFunctions.RHTower.HyperbolicBallTransform

open MeasureTheory UpperHalfPlane ModularGroup Set Metric Module
open scoped MatrixGroups ENNReal InnerProductSpace

/-!
# The Sarnak–Xue multiplicity bound for `Γ(p)`

If a `Γ(p)` Maass cusp form with eigenvalue `λ = s(1-s) ∈ (0, 1/4)` exists (`p = N + 1` an odd prime),
its `SL(2,ℤ)`-translate span `W` has `N ≤ 2 dim W`. With the coset-sum inner product and an orthonormal
basis `(b_j)`, `dim W = Σ_j ∫_𝒟 Σ_q |b_j(q̃z)|²`; the cusp above height `p` carries at most a third of each
term, and on the rest the pointwise pretrace bound, conjugation invariance of the kernel sum, the kernel sum
bound and `|SL(2,ℤ)/Γ(p)| ≤ p³` (`card_deck_le`) give
`N ≤ 3 vol(𝒟) p³ kb / ((cosh R)^s/16)²` (`dim_le`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueDimension

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SarnakXueInner
open GaloisForLFunctions.RHTower.SarnakXuePointwise
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace

noncomputable section

variable {N : ℕ} {lam : ℝ}

/-- On any subspace with the coset-sum inner product, a pointwise bound `|u(v)|² ≤ M ⟨u,u⟩` gives
`Σ_j |b_j(v)|² ≤ M` for every orthonormal basis. -/
theorem onb_eval_le (W : Submodule ℂ (V N lam)) [FiniteDimensional ℂ W] (v : ℍ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ u : W, ‖u.1.1 v‖ ^ 2 ≤ M * (ip u.1 u.1).re) :
    letI : InnerProductSpace.Core ℂ W := core W
    letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore _
    ∑ j, Complex.normSq ((stdOrthonormalBasis ℂ W j).1.1 v) ≤ M := by
  letI : InnerProductSpace.Core ℂ W := core W
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore _
  let φ : W →ₗ[ℂ] ℂ :=
    { toFun := fun u => u.1.1 v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply sum_normSq_le (stdOrthonormalBasis ℂ W) φ hM
  intro u
  have hn : ‖u‖ ^ 2 = (ip u.1 u.1).re := by
    rw [@norm_sq_eq_re_inner ℂ]
    rfl
  rw [hn, Complex.normSq_eq_norm_sq]
  exact h u


end

section card
theorem card_SL_le (p : ℕ) [Fact p.Prime] : Fintype.card SL(2, ZMod p) ≤ p ^ 3 := by
  classical
  let f : SL(2, ZMod p) → ZMod p × ZMod p × ZMod p := fun M =>
    (M 0 0, M 0 1, if M 0 0 = 0 then M 1 1 else M 1 0)
  have hdet : ∀ M : SL(2, ZMod p), M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    intro M; have := M.2; rw [Matrix.det_fin_two] at this; exact this
  have hinj : Function.Injective f := by
    intro M M' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨ha, hb, hc⟩ := h
    have d1 := hdet M; have d2 := hdet M'
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    by_cases h0 : M 0 0 = 0
    · have h0' : M' 0 0 = 0 := ha ▸ h0
      rw [if_pos h0, if_pos h0'] at hc
      rw [h0, zero_mul, zero_sub] at d1
      rw [h0', zero_mul, zero_sub] at d2
      have hb0 : M 0 1 ≠ 0 := by intro hz; rw [hz, zero_mul, neg_zero] at d1; exact zero_ne_one d1
      have hcc : M 1 0 = M' 1 0 := by
        have : M 0 1 * M 1 0 = M 0 1 * M' 1 0 := by linear_combination -d1 + d2 - (M' 1 0) * hb
        exact mul_left_cancel₀ hb0 this
      fin_cases i <;> fin_cases j <;> simp_all
    · have h0' : M' 0 0 ≠ 0 := ha ▸ h0
      rw [if_neg h0, if_neg h0'] at hc
      have hdd : M 1 1 = M' 1 1 := by
        have : M 0 0 * M 1 1 = M 0 0 * M' 1 1 := by linear_combination d1 - d2 + (M 0 1) * hc + (M' 1 0) * hb - (M' 1 1) * ha
        exact mul_left_cancel₀ h0 this
      fin_cases i <;> fin_cases j <;> simp_all
  calc Fintype.card SL(2, ZMod p) ≤ Fintype.card (ZMod p × ZMod p × ZMod p) :=
        Fintype.card_le_of_injective f hinj
    _ = p ^ 3 := by simp [Fintype.card_prod, ZMod.card]; ring

/-- The number of cosets of `Γ(p)` in `SL(2,ℤ)` is at most `p³`. -/
theorem card_deck_le (N : ℕ) [Fact (N + 1).Prime] : Fintype.card (Deck N) ≤ (N + 1) ^ 3 := by
  classical
  let φ : SL(2, ℤ) →* SL(2, ZMod (N + 1)) :=
    Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (N + 1)))
  have hinj : Function.Injective (QuotientGroup.kerLift φ) := QuotientGroup.kerLift_injective φ
  have h := Fintype.card_le_of_injective (α := Deck N) (β := SL(2, ZMod (N + 1)))
    (QuotientGroup.kerLift φ) hinj
  exact h.trans (card_SL_le (N + 1))

end card

noncomputable section
open SarnakXueKernel SarnakXueCuspRegion SarnakXueCuspMode HyperbolicBallTransform MaassCongruenceL2

/-- The explicit kernel bound at height `y ≤ p`. -/
def kb (p : ℕ) (R : ℝ) (K : ℕ) (C ε : ℝ) : ℝ :=
  16 * Real.cosh R * Real.sqrt 2 * (32 * (1 + C * 9 ^ ε) * ((2 : ℝ) ^ (K + 2)) ^ ε *
    (4 + 2 * K * ((p : ℝ) + 1) / p + 4 * K * Real.sqrt (2 ^ K) / (p : ℝ) ^ 3))

theorem edge_le_third (hN : 2 ≤ N) : edge N ≤ ((N + 1 : ℕ) : ℝ) / 3 := by
  unfold edge
  have hp : (3 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ N + 1 by omega)
  have hpi := Real.pi_gt_three
  apply max_le (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Upper multiplicity bound.** If a `Γ(p)` Maass cusp form with eigenvalue `λ = s(1-s) ∈ (0, 1/4)`
exists (`p = N + 1` an odd prime), then for every `R ≥ 2`, `K` with `cosh 2R < 2^K` and divisor bound
`d(n) ≤ C n^ε`,
`N ≤ 3 vol(𝒟) p³ · kb / ((cosh R)^s / 16)²`. -/
theorem dim_le (hp : (N + 1).Prime) (hN : 2 ≤ N) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {s : ℝ} (hs : s * (1 - s) = lam) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    {R : ℝ} (hR : 2 ≤ R) (K : ℕ) (hK : Real.cosh (2 * R) < 2 ^ K)
    {ε C : ℝ} (hε : 0 < ε) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε) :
    (N : ℝ) ≤ 3 * (volume fd).toReal * ((N + 1 : ℕ) : ℝ) ^ 3 *
      (kb (N + 1) R K C ε / (Real.cosh R ^ s / 16) ^ 2) := by
  haveI : Fact (N + 1).Prime := ⟨hp⟩
  have hp2 : N + 1 ≠ 2 := by omega
  set p : ℕ := N + 1 with hpdef
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 3 ≤ p by omega)
  set u0 : V N lam := principalMaassCuspEigenformToHeckeEigenspace N lam f
  have hu0 : u0 ≠ 0 := principalMaassCuspEigenformToHeckeEigenspace_ne_zero N lam f
  set W := SarnakXue.translateSpan N lam u0
  obtain ⟨hfin, hdim⟩ := SarnakXue.exceptional_translateSpan_dim N lam hp lam.2 u0 hu0
  haveI := hfin
  letI : InnerProductSpace.Core ℂ W := core W
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore _
  set b := stdOrthonormalBasis ℂ W
  -- the transform
  set T := ∫ w in closedBall I R, w.im ^ s
  have hT : Real.cosh R ^ s / 16 ≤ T := ballTransform_lower hR hs0 hs2
  have hT0 : 0 < Real.cosh R ^ s / 16 := by
    have := Real.rpow_pos_of_pos (Real.cosh_pos R) s; positivity
  have hTpos : 0 < T := hT0.trans_le hT
  set KB := kb p R K C ε
  have hKB : 0 ≤ KB := by
    simp only [KB, kb]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 ^ (K + 2) by positivity) ε
    positivity
  set M := KB / T ^ 2
  have hM : 0 ≤ M := by positivity
  -- pointwise bound on the compact part
  have hpt : ∀ z ∈ fd, z.im ≤ p → ∀ q : Deck N,
      ∑ j, Complex.normSq ((b j).1.1 (q.out • z)) ≤ M := by
    intro z hz hzy q
    have hx : |z.re| ≤ 1 / 2 := hz.2
    have hy : 1 / 2 ≤ z.im := by
      have := three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith [z.im_pos]
    have hker := kernel_sum_le hp2 hx hy hε hC0 hC (by linarith : (0 : ℝ) ≤ R) K hK
    have hLz : kernelSum p z R ≤ ENNReal.ofReal KB := by
      refine hker.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [KB, kb]
      have h1 : 2 * (K : ℝ) * (z.im + 1) / p ≤ 2 * K * ((p : ℝ) + 1) / p := by gcongr
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 ^ (K + 2) by positivity) ε
      gcongr
    have hL : kernelSum p (q.out • z) R ≠ ⊤ := by
      rw [kernelSum_smul]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLz
    have hLr : (kernelSum p (q.out • z) R).toReal ≤ KB := by
      rw [kernelSum_smul]
      exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLz)
        ENNReal.ofReal_ne_top).mpr hLz |>.trans (ENNReal.toReal_ofReal hKB).le
    apply onb_eval_le W (q.out • z) hM
    intro u
    have h := pointwise_bound u.1 hs (q.out • z) R hL
    have hre := ip_self_re_nonneg u.1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hLr hre]
  -- the orthonormal basis vectors
  set D : Fin (finrank ℂ W) → ℍ → ℝ := fun j z => ∑ q : Deck N, Complex.normSq ((b j).1.1 (q.out • z))
  have hone : ∀ j, (ip (b j).1 (b j).1).re = 1 := by
    intro j
    have h1 : ‖b j‖ = 1 := b.orthonormal.1 j
    have h2 : ‖b j‖ ^ 2 = (ip (b j).1 (b j).1).re := by
      rw [@norm_sq_eq_re_inner ℂ]; rfl
    rw [← h2, h1, one_pow]
  have hne : ∀ j, (b j).1 ≠ 0 := by
    intro j h
    have := hone j
    rw [h] at this
    have h0 : ip (0 : V N lam) 0 = 0 := by
      unfold ip ipDensity; simp
    rw [h0, Complex.zero_re] at this
    exact zero_ne_one this
  have hip : ∀ j, (ip (b j).1 (b j).1).re = ∫ z in fd, D j z := by
    intro j; rw [ip_self, Complex.ofReal_re]
  have hdens : ∀ j z, density N (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N (b j).1 (hne j)) z =
      D j z := fun j z => density_eq (b j).1 (hne j) z
  have hint : ∀ j, IntegrableOn (D j) fd := by
    intro j
    exact (density_integrable N (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N (b j).1 (hne j))).congr
      (Filter.Eventually.of_forall (hdens j))
  have hmeas : MeasurableSet {z : ℍ | z.im ≤ (p : ℝ)} :=
    measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const
  have hcusp : ∀ j, ∫ z in fd, D j z ≤ (3 / 2) * ∫ z in fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}, D j z := by
    intro j
    have hfrac := fd_cusp_fraction N (by omega) lam
      (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N (b j).1 (hne j))
    simp_rw [hdens] at hfrac
    have hnn : 0 ≤ ∫ z in fd, D j z :=
      setIntegral_nonneg isClosed_fd.measurableSet
        (fun z _ => Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))
    have hsplit := integral_inter_add_sdiff hmeas (hint j)
    have hdiff : fd \ {z : ℍ | z.im ≤ (p : ℝ)} = fd ∩ {z : ℍ | (p : ℝ) < z.im} := by
      ext z; simp [not_le]
    rw [hdiff] at hsplit
    have he := edge_le_third (N := N) hN
    have hpp : (0 : ℝ) < p := by linarith
    have hup : ∫ z in fd ∩ {z : ℍ | (p : ℝ) < z.im}, D j z ≤ (1 / 3) * ∫ z in fd, D j z := by
      have h3 : (p : ℝ) * ∫ z in fd ∩ {z : ℍ | (p : ℝ) < z.im}, D j z ≤ (p / 3) * ∫ z in fd, D j z :=
        hfrac.trans (mul_le_mul_of_nonneg_right he hnn)
      have : (p : ℝ) * ∫ z in fd ∩ {z : ℍ | (p : ℝ) < z.im}, D j z ≤
          (p : ℝ) * ((1 / 3) * ∫ z in fd, D j z) := by linarith
      exact le_of_mul_le_mul_left this hpp
    linarith
  -- summing over the basis
  have hbound : ∀ z ∈ fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}, ∑ j, D j z ≤ Fintype.card (Deck N) * M := by
    intro z hz
    simp only [D]
    rw [Finset.sum_comm]
    calc ∑ q : Deck N, ∑ j, Complex.normSq ((b j).1.1 (q.out • z)) ≤ ∑ _q : Deck N, M :=
          Finset.sum_le_sum (fun q _ => hpt z hz.1 hz.2 q)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfdfin : volume (fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}) < ⊤ :=
    (measure_mono inter_subset_left).trans_lt GaloisForLFunctions.HTGeometry.volume_fd_lt_top
  have hsum : (finrank ℂ W : ℝ) ≤ (3 / 2) * (Fintype.card (Deck N) * M) * (volume fd).toReal := by
    calc (finrank ℂ W : ℝ) = ∑ j, (ip (b j).1 (b j).1).re := by
          simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ = ∑ j, ∫ z in fd, D j z := by simp only [hip]
      _ ≤ ∑ j, (3 / 2) * ∫ z in fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}, D j z := Finset.sum_le_sum (fun j _ => hcusp j)
      _ = (3 / 2) * ∫ z in fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}, ∑ j, D j z := by
          rw [← Finset.mul_sum, integral_finsetSum]
          intro j _; exact (hint j).mono_set inter_subset_left
      _ ≤ (3 / 2) * ∫ z in fd ∩ {z : ℍ | z.im ≤ (p : ℝ)}, (Fintype.card (Deck N) * M) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact setIntegral_mono_on (integrable_finsetSum _ (fun j _ => (hint j).mono_set inter_subset_left))
            (integrableOn_const hfdfin.ne) (isClosed_fd.measurableSet.inter hmeas) hbound
      _ ≤ (3 / 2) * (Fintype.card (Deck N) * M) * (volume fd).toReal := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm (ENNReal.toReal _), ← mul_assoc]
          have hc : 0 ≤ (3 / 2) * ((Fintype.card (Deck N) : ℝ) * M) := by positivity
          exact mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono GaloisForLFunctions.HTGeometry.volume_fd_ne_top (measure_mono inter_subset_left)) hc
  have hcard : (Fintype.card (Deck N) : ℝ) ≤ (p : ℝ) ^ 3 := by exact_mod_cast card_deck_le N
  have hMle : M ≤ KB / (Real.cosh R ^ s / 16) ^ 2 := by
    apply div_le_div_of_nonneg_left hKB (by positivity)
    exact pow_le_pow_left₀ hT0.le hT 2
  have hvol : 0 ≤ (volume fd).toReal := ENNReal.toReal_nonneg
  have h2 : (N : ℝ) ≤ 2 * (finrank ℂ W : ℝ) := by exact_mod_cast hdim
  calc (N : ℝ) ≤ 2 * ((3 / 2) * (Fintype.card (Deck N) * M) * (volume fd).toReal) := by linarith
    _ = 3 * (volume fd).toReal * Fintype.card (Deck N) * M := by ring
    _ ≤ 3 * (volume fd).toReal * (p : ℝ) ^ 3 * (KB / (Real.cosh R ^ s / 16) ^ 2) := by
        gcongr

end
end GaloisForLFunctions.RHTower.SarnakXueDimension
