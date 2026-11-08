import GaloisForLFunctions.BlackHoleRingdown.TheMultiplicityOfTheHeckeModes

/-!
# The parity of the Hecke modes

The mirror `ι z = -z̄` of the modular horizon acts on every cusp space. It commutes with the Laplacian, since
in the chart it is the reflection `x ↦ -x`, and with every Hecke operator: `ι(pz) = p ιz` and
`ι((z+b)/p) = (ιz - b)/p`, and `b ↦ -b` permutes the residues up to an integer translation. It exchanges the
Fourier modes `a_n` and `a_{-n}`.

**Strong multiplicity one.** A joint eigenform of the Laplacian, of all `T_p` and of the mirror, with parity
`ε`, has `a_{-1} = ε a_1`; by Hecke rigidity it is determined by `a_1`, which lies in a line. So each joint
eigenspace of definite parity has dimension at most one (`finrank_paritySpace_le_one`). Every eigenvalue of
the cusp spectrum carries such an eigenform (`exists_parity_heckeMaassForm`): `h ± h ∘ ι` for a Hecke
eigenform `h`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.Gamma0MaassHecke
  GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos atImInfty)
open OddCusp (mirror coe_mirror mirror_im mirrorSL mirror_smul)

namespace HeckeCusp

/-! ### The mirror in the chart -/

/-- The reflection `ζ ↦ -ζ̄` of the chart. -/
def reflL : ℂ →L[ℝ] ℂ := -(Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem reflL_apply (ζ : ℂ) : reflL ζ = -(starRingEnd ℂ) ζ := by
  simp [reflL]

theorem reflL_im (ζ : ℂ) : (reflL ζ).im = ζ.im := by
  simp [reflL_apply]

theorem reflL_one : reflL 1 = -1 := by simp [reflL_apply]

theorem reflL_I : reflL I = I := by simp [reflL_apply]

theorem mirror_ofComplex {ζ : ℂ} (hζ : 0 < ζ.im) : mirror (ofComplex ζ) = ofComplex (reflL ζ) := by
  have h2 : 0 < (reflL ζ).im := by rw [reflL_im]; exact hζ
  have e1 : ((ofComplex ζ : UpperHalfPlane) : ℂ) = ζ := by rw [ofComplex_apply_of_im_pos hζ]
  have e2 : ((ofComplex (reflL ζ) : UpperHalfPlane) : ℂ) = reflL ζ := by rw [ofComplex_apply_of_im_pos h2]
  apply UpperHalfPlane.ext
  rw [coe_mirror, e1, e2, reflL_apply]

theorem mirror_point (x y : ℝ) (hy : 0 < y) :
    mirror (ofComplex (SelbergMaassMean.point x y)) = ofComplex (SelbergMaassMean.point (-x) y) := by
  rw [mirror_ofComplex (point_im_pos hy)]
  congr 1
  rw [reflL_apply]
  apply Complex.ext <;> simp [SelbergMaassMean.point]

/-- **A second directional derivative under the reflection.** -/
theorem dir_dir_refl {G : ℂ → ℂ} {ζ : ℂ} (hG : ContDiffAt ℝ 2 G (reflL ζ)) (v : ℂ) :
    dir v (dir v (G ∘ reflL)) ζ = dir (reflL v) (dir (reflL v) G) (reflL ζ) := by
  have hev : ∀ᶠ ζ' in 𝓝 ζ, DifferentiableAt ℝ G (reflL ζ') :=
    reflL.continuous.continuousAt.tendsto.eventually
      ((hG.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have he : dir v (G ∘ reflL) =ᶠ[𝓝 ζ] (dir (reflL v) G) ∘ reflL := by
    filter_upwards [hev] with ζ' h
    show fderiv ℝ (G ∘ reflL) ζ' v = fderiv ℝ G (reflL ζ') (reflL v)
    rw [(h.hasFDerivAt.comp ζ' reflL.hasFDerivAt).fderiv]
    rfl
  have hd : DifferentiableAt ℝ (dir (reflL v) G) (reflL ζ) :=
    (dir_contDiffAt hG (reflL v)).differentiableAt (by norm_num)
  show fderiv ℝ (dir v (G ∘ reflL)) ζ v = _
  rw [he.fderiv_eq, (hd.hasFDerivAt.comp ζ reflL.hasFDerivAt).fderiv]
  rfl

theorem dir_neg_one {G : ℂ → ℂ} (w : ℂ) : dir (-1) (dir (-1) G) w = dir 1 (dir 1 G) w := by
  have h1 : dir (-1) G = fun w => -dir 1 G w := by
    funext w
    simp only [dir, map_neg]
  rw [h1]
  show fderiv ℝ (-(dir 1 G)) w (-1) = fderiv ℝ (dir 1 G) w 1
  rw [fderiv_neg]
  simp

variable {lam : ℝ} {g : UpperHalfPlane → ℂ}

theorem isMaassEigenfunction_comp_mirror (hg : IsMaassEigenfunction lam g) :
    IsMaassEigenfunction lam (g ∘ mirror) := by
  have hΩ : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcomp : ∀ ζ : ℂ, 0 < ζ.im → ((g ∘ mirror) ∘ ofComplex) ζ = ((g ∘ ofComplex) ∘ reflL) ζ := by
    intro ζ hζ
    simp only [Function.comp]
    rw [mirror_ofComplex hζ]
  have hmaps : MapsTo reflL {ζ : ℂ | 0 < ζ.im} {ζ : ℂ | 0 < ζ.im} := fun ζ hζ => by
    show 0 < (reflL ζ).im
    rw [reflL_im]
    exact hζ
  refine ⟨?_, fun z => ?_⟩
  · unfold IsRealSmoothUpperHalfPlane
    exact (hg.1.comp reflL.contDiff.contDiffOn hmaps).congr fun ζ hζ => hcomp ζ hζ
  · have hz : 0 < (z : ℂ).im := z.im_pos
    have hev : ((g ∘ mirror) ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)] ((g ∘ ofComplex) ∘ reflL) := by
      filter_upwards [hΩ.mem_nhds hz] with ζ hζ using hcomp ζ hζ
    have hG : ContDiffAt ℝ 2 (g ∘ ofComplex) (reflL z) :=
      hg.1.contDiffAt (hΩ.mem_nhds (by show 0 < (reflL (z : ℂ)).im; rw [reflL_im]; exact hz))
    have h1 := dir_dir_congr hev 1
    have h2 := dir_dir_congr hev I
    rw [dir_dir_refl hG, reflL_one, dir_neg_one] at h1
    rw [dir_dir_refl hG, reflL_I] at h2
    have hm : ((mirror z : UpperHalfPlane) : ℂ) = reflL z := by rw [coe_mirror, reflL_apply]
    have he := hg.2 (mirror z)
    unfold positiveHyperbolicLaplacian at he ⊢
    rw [mirror_im, hm] at he
    change -((z.im : ℂ)) ^ (2 : ℕ) * (dir 1 (dir 1 ((g ∘ mirror) ∘ ofComplex)) z +
      dir I (dir I ((g ∘ mirror) ∘ ofComplex)) z) = (lam : ℂ) * g (mirror z)
    rw [h1, h2]
    exact he

/-! ### Hecke commutes with the mirror -/

theorem sum_neg_residues (p : ℕ) [hp : Fact p.Prime] {F : ℂ → ℂ}
    (hper : ∀ w : ℂ, 0 < w.im → F (w + 1) = F w) {w : ℂ} (hw : 0 < w.im) :
    ∑ b : ZMod p, F ((w - (b.val : ℂ)) / p) = ∑ b : ZMod p, F ((w + (b.val : ℂ)) / p) := by
  rw [← Equiv.sum_comp (Equiv.neg (ZMod p)) (fun b : ZMod p => F ((w + (b.val : ℂ)) / p))]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.neg_apply]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [ZMod.neg_val]
  split_ifs with hb
  · subst hb
    simp
  · have hlt : b.val ≤ p := (ZMod.val_lt b).le
    have him : 0 < ((w - (b.val : ℂ)) / p).im := by
      have hp' : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      rw [show ((w - (b.val : ℂ)) / p).im = w.im / p by
        rw [Complex.div_natCast_im, Complex.sub_im, Complex.natCast_im, sub_zero]]
      positivity
    have e : (w + ((p - b.val : ℕ) : ℂ)) / p = (w - (b.val : ℂ)) / p + 1 := by
      rw [Nat.cast_sub hlt]
      field_simp
      ring
    rw [e, hper _ him]

/-- **The Hecke operators commute with the mirror.** -/
theorem heckeH_comp_mirror (p : ℕ) [hp : Fact p.Prime] (hg : g ∈ cuspSpace lam) :
    heckeH p (g ∘ mirror) = heckeH p g ∘ mirror := by
  funext z
  have hz : 0 < (z : ℂ).im := z.im_pos
  rw [Function.comp_apply, heckeH_eq, heckeH_eq, coe_mirror]
  unfold heckeT
  have hterm : ∀ i : Option (ZMod p), ((g ∘ mirror) ∘ ofComplex) (heckeAct p i z) =
      (g ∘ ofComplex) (reflL (heckeAct p i z)) := by
    intro i
    simp only [Function.comp]
    rw [mirror_ofComplex (heckeAct_im_pos p i hz)]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp only [Fintype.sum_option, heckeAct]
  have hR : -(starRingEnd ℂ) (z : ℂ) = reflL z := (reflL_apply _).symm
  rw [hR]
  have h1 : reflL ((p : ℂ) * z) = p * reflL z := by
    rw [reflL_apply, reflL_apply, map_mul, Complex.conj_natCast]
    ring
  have h2 : ∀ b : ZMod p, reflL (((z : ℂ) + (b.val : ℂ)) / p) = (reflL z - (b.val : ℂ)) / p := by
    intro b
    rw [reflL_apply, reflL_apply, map_div₀, map_add, Complex.conj_natCast, Complex.conj_natCast]
    ring
  simp only [h1, h2]
  rw [sum_neg_residues p (periodic_comp hg) (by rw [reflL_im]; exact hz)]

/-- **The mirror exchanges the Fourier modes `a_n` and `a_{-n}`.** -/
theorem fourierCoeff_comp_mirror (hg : g ∈ cuspSpace lam) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    fourierCoeff (g ∘ mirror) n y = fourierCoeff g (-n) y := by
  unfold fourierCoeff SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  congr 1
  set G : ℝ → ℂ := fun u => (g ∘ ofComplex) (SelbergMaassMean.point u y) with hG
  have hval : ∀ x : ℝ, ((g ∘ mirror) ∘ ofComplex) (SelbergMaassMean.point x y) = G (-x) := by
    intro x
    simp only [Function.comp, hG]
    rw [mirror_point x y hy]
  simp_rw [hval]
  have hk : ∀ x : ℝ, _root_.RHTower.deningerFourierKernel 1 n x =
      _root_.RHTower.deningerFourierKernel 1 (-n) (-x) := by
    intro x
    unfold _root_.RHTower.deningerFourierKernel
    congr 1
    push_cast
    ring
  simp_rw [hk]
  rw [intervalIntegral.integral_comp_neg (fun x => _root_.RHTower.deningerFourierKernel 1 (-n) x * G x)]
  have hper : Function.Periodic (fun x => _root_.RHTower.deningerFourierKernel 1 (-n) x * G x) 1 := by
    intro x
    have hGp : G (x + 1) = G x := by
      have h := periodic_comp hg (SelbergMaassMean.point x y) (point_im_pos hy)
      simp only [hG]
      rw [show SelbergMaassMean.point (x + 1) y = SelbergMaassMean.point x y + 1 by
        simp [SelbergMaassMean.point]; ring]
      exact h
    have hKp : _root_.RHTower.deningerFourierKernel 1 (-n) (x + 1) =
        _root_.RHTower.deningerFourierKernel 1 (-n) x := by
      unfold _root_.RHTower.deningerFourierKernel
      rw [show -(2 * Real.pi * I * ((-n : ℤ) : ℂ) * (((x + 1 : ℝ)) : ℂ)) / ((1 : ℝ) : ℂ) =
          -(2 * Real.pi * I * ((-n : ℤ) : ℂ) * (x : ℂ)) / ((1 : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only
    rw [hKp, hGp]
  rw [show (-1 : ℝ) = 0 + -1 by ring, show (-0 : ℝ) = (-1) + 1 by ring]
  rw [show ((0 : ℝ) + -1) = -1 by ring]
  exact hper.intervalIntegral_add_eq (-1) 0 |>.trans (by norm_num)

/-- **The mirror preserves the cusp space.** -/
theorem comp_mirror_mem_cuspSpace (hg : g ∈ cuspSpace lam) : g ∘ mirror ∈ cuspSpace lam := by
  refine ⟨fun A z => ?_, isMaassEigenfunction_comp_mirror hg.2.1, ?_, fun y hy => ?_⟩
  · simp only [Function.comp]
    rw [mirror_smul, hg.1]
  · have ht : Tendsto mirror atImInfty atImInfty := by
      rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
      have : (UpperHalfPlane.im ∘ mirror) = UpperHalfPlane.im := funext fun z => mirror_im z
      rw [this]
      exact tendsto_comap
    exact hg.2.2.1.comp ht
  · have h := fourierCoeff_comp_mirror hg 0 hy
    rw [neg_zero, fourierCoeff_zero hg hy] at h
    rw [fourierCoeff, coefficient_zero] at h
    exact h

/-! ### Strong multiplicity one -/

/-- The joint eigenspace of the Laplacian, the Hecke operators and the mirror with eigenvalue `ε`. -/
def paritySpace (lam : ℝ) (c : ℕ → ℂ) (ε : ℂ) : Submodule ℂ (UpperHalfPlane → ℂ) where
  carrier := {g | g ∈ jointSpace lam c ∧ g ∘ mirror = ε • g}
  add_mem' := by
    rintro g h ⟨hg, hgm⟩ ⟨hh, hhm⟩
    refine ⟨Submodule.add_mem _ hg hh, ?_⟩
    funext z
    have h1 := congrFun hgm z
    have h2 := congrFun hhm z
    simp only [Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h1, h2]
    ring
  zero_mem' := ⟨Submodule.zero_mem _, by funext z; simp⟩
  smul_mem' a g := by
    rintro ⟨hg, hgm⟩
    refine ⟨Submodule.smul_mem _ a hg, ?_⟩
    funext z
    have h1 := congrFun hgm z
    simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1]
    ring

instance (lam : ℝ) (c : ℕ → ℂ) (ε : ℂ) : FiniteDimensional ℂ (paritySpace lam c ε) :=
  Module.Finite.of_injective (Submodule.inclusion (fun _ h => h.1.1 : paritySpace lam c ε ≤ cuspSpace lam))
    (Submodule.inclusion_injective _)

/-- **Strong multiplicity one.** Each joint eigenspace of the Laplacian, the Hecke operators and the mirror has
dimension at most one. -/
theorem finrank_paritySpace_le_one (lam : ℝ) (c : ℕ → ℂ) (ε : ℂ) :
    Module.finrank ℂ (paritySpace lam c ε) ≤ 1 := by
  have hle : paritySpace lam c ε ≤ cuspSpace lam := fun _ h => h.1.1
  set Φ := LinearMap.codRestrict (LinearMap.range (modeMap lam 1))
    (modeMap lam 1 ∘ₗ Submodule.inclusion hle) fun g => LinearMap.mem_range_self _ _
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have h1 : ((Φ g : LinearMap.range (modeMap lam 1)) : ℝ → ℂ) = 0 := by rw [hg]; rfl
    have ha1 : ∀ y : ℝ, 0 < y → fourierCoeff g.1 1 y = 0 := by
      intro y hy
      have := congrFun h1 y
      simp only [Φ, Pi.zero_apply] at this
      change (if 0 < y then fourierCoeff g.1 1 y else 0) = 0 at this
      rwa [if_pos hy] at this
    apply Subtype.ext
    refine eq_zero_of_firstCoeff_eq_zero g.2.1.1 (fun p _ => ⟨c p, g.2.1.2 p⟩) ha1 fun y hy => ?_
    have hm := fourierCoeff_comp_mirror g.2.1.1 1 hy
    rw [g.2.2] at hm
    have hsm : fourierCoeff (ε • g.1) 1 y = ε * fourierCoeff g.1 1 y := by
      unfold fourierCoeff
      rw [show (ε • g.1) ∘ ofComplex = fun w => ε * (g.1 ∘ ofComplex) w from by funext w; simp,
        coefficient_mul]
    rw [hsm, ha1 y hy, mul_zero] at hm
    exact hm.symm
  have := LinearMap.finrank_le_finrank_of_injective hinj
  exact this.trans (finrank_range_modeMap_le lam 1)

/-- **Every eigenvalue of the cusp spectrum carries a Hecke–Maass form of definite parity**, and the joint
eigenspace of that parity is a line. -/
theorem exists_parity_heckeMaassForm (i : CuspEigenIndex 0) :
    ∃ (c : ℕ → ℂ) (ε : ℂ), (ε = 1 ∨ ε = -1) ∧ Module.finrank ℂ (paritySpace i.1 c ε) = 1 := by
  obtain ⟨h, hh, hh0, hH⟩ := exists_heckeEigenform (cuspSpace_ne_bot i)
  set c : ℕ → ℂ := fun p => if hp : p.Prime then (haveI := Fact.mk hp; Classical.choose (hH p)) else 0 with hcdef
  have hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p h = c p • h := by
    intro p hp
    simp only [hcdef, dif_pos hp.out]
    exact Classical.choose_spec (hH p)
  have hm : h ∘ mirror ∈ cuspSpace i.1 := comp_mirror_mem_cuspSpace hh
  have hmc : ∀ (p : ℕ) [Fact p.Prime], heckeH p (h ∘ mirror) = c p • (h ∘ mirror) := by
    intro p _
    rw [heckeH_comp_mirror p hh, hc p]
    rfl
  have hmm : (h ∘ mirror) ∘ mirror = h := funext fun z => by simp [OddSector.mirror_mirror]
  by_cases hplus : h + h ∘ mirror = 0
  · -- the odd part is nonzero
    refine ⟨c, -1, Or.inr rfl, le_antisymm (finrank_paritySpace_le_one _ _ _) ?_⟩
    have hmem : h - h ∘ mirror ∈ paritySpace i.1 c (-1) := by
      refine ⟨⟨Submodule.sub_mem _ hh hm, fun p _ => ?_⟩, ?_⟩
      · rw [show h - h ∘ mirror = h + (-1 : ℂ) • (h ∘ mirror) by funext z; simp; ring, heckeH_add,
          heckeH_smul, hc p, hmc p]
        funext z
        simp
        ring
      · funext z
        have := congrFun hmm z
        simp only [Function.comp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
        ring
    have hne : h - h ∘ mirror ≠ 0 := by
      intro h0
      apply hh0
      funext z
      have h1 := congrFun hplus z
      have h2 := congrFun h0 z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Function.comp] at h1 h2 ⊢
      linear_combination (h1 + h2) / 2
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hmem⟩, fun h0 => hne (congrArg Subtype.val h0)⟩
  · refine ⟨c, 1, Or.inl rfl, le_antisymm (finrank_paritySpace_le_one _ _ _) ?_⟩
    have hmem : h + h ∘ mirror ∈ paritySpace i.1 c 1 := by
      refine ⟨⟨Submodule.add_mem _ hh hm, fun p _ => ?_⟩, ?_⟩
      · rw [heckeH_add, hc p, hmc p, smul_add]
      · funext z
        have := congrFun hmm z
        simp only [Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this ⊢
        rw [this]
        ring
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hmem⟩, fun h0 => hplus (congrArg Subtype.val h0)⟩

end HeckeCusp

end GaloisForLFunctions.BlackHoleRingdown
