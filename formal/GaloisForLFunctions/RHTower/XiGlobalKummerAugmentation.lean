import GaloisForLFunctions.RHTower.XiExponentialTranslateSquareRigidity
import GaloisForLFunctions.RHTower.XiGlobalKummerTranslatedSection

/-!
# The second global division class of the translated Legendre section

The positive companion `1+n^(-s)*xi` and its product with Xi remain nonsquare
on the joint marked extension. Thus the additional class of the translated
section is independent of the common class carried by the original sections.
-/

open Complex Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_algebraMap constPlane_injective

/-- Companion factor giving the additional class of the translated section. -/
def augmentationFactor (n : ℕ) (s : ℂ) : ℂ := 2 - deletionFactor n s

theorem augmentationFactor_differentiable (n : ℕ) : Differentiable ℂ (augmentationFactor n) :=
  (differentiable_const 2).sub (deletionFactor_differentiable n)

def augmentationElement (n : ℕ) : K :=
  ofMeromorphic (augmentationFactor n) (fun z => ((augmentationFactor_differentiable n).analyticAt z).meromorphicAt)

theorem augmentationFactor_conj (n : ℕ) (s : ℂ) :
    augmentationFactor n (conj s) = conj (augmentationFactor n s) := by
  simp only [augmentationFactor, deletionFactor_conj, map_sub, map_ofNat]

theorem augmentationFactor_real_im (n : ℕ) (t : ℝ) :
    (augmentationFactor n t).im = 0 := by
  rw [augmentationFactor, ← realFactor_cast]
  simp

theorem augmentationFactor_real_pos (n : ℕ) (t : ℝ) :
    0 < (augmentationFactor n t).re := by
  rw [augmentationFactor, ← realFactor_cast]
  norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
  dsimp [realFactor]
  have hp := mul_pos (Real.exp_pos (-t * Real.log n)) (xi_real_pos t)
  linarith

theorem augmentationElement_not_isSquare {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (augmentationElement n) := by
  intro hs
  obtain ⟨g, hgd, hsq⟩ := entire_sqrt_of_isSquare_plane (augmentationFactor_differentiable n) hs
  apply not_exists_entire_sqrt_one_add_exp_mul_xi
    (h := -Real.log n) (neg_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))))
  refine ⟨g, hgd, fun s => ?_⟩
  rw [hsq]
  dsimp [augmentationFactor, deletionFactor]
  rw [Complex.ofReal_neg]
  rw [show -s * (Real.log n : ℂ) = -(Real.log n : ℂ) * s by ring]
  ring

theorem xi_mul_augmentationElement_not_isSquare (n : ℕ) :
    ¬ IsSquare (xiElement * augmentationElement n) := by
  intro hs
  have hd : Differentiable ℂ (fun z => xi z * augmentationFactor n z) :=
    xi_differentiable.mul (augmentationFactor_differentiable n)
  obtain ⟨g, hgd, hsq⟩ := entire_sqrt_of_isSquare_plane hd hs
  obtain ⟨rho, hrho, hodd⟩ := exists_odd_order_zero_xi
  have hunit : augmentationFactor n rho ≠ 0 := by
    norm_num [augmentationFactor, deletionFactor, hrho]
  have hord : analyticOrderAt (fun z => g z ^ 2) rho = analyticOrderAt xi rho := by
    rw [show (fun z => g z ^ 2) = (fun z => xi z * augmentationFactor n z) from funext hsq]
    rw [show (fun z => xi z * augmentationFactor n z) = xi * augmentationFactor n by rfl,
      analyticOrderAt_mul (xi_differentiable.analyticAt rho) ((augmentationFactor_differentiable n).analyticAt rho),
      ((augmentationFactor_differentiable n).analyticAt rho).analyticOrderAt_eq_zero.mpr hunit, add_zero]
  have heven : Even (analyticOrderAt xi rho).toNat := by
    rw [← hord, show (fun z => g z ^ 2) = g ^ (2 : ℕ) by rfl, analyticOrderAt_pow (hgd.analyticAt rho)]
    rw [show (2 • analyticOrderAt g rho).toNat = 2 * (analyticOrderAt g rho).toNat by
      rw [nsmul_eq_mul, ENat.toNat_mul]
      norm_num]
    exact even_two.mul_right _
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- A positive real entire factor cannot hide any nonempty marked-product sign change. -/
theorem positive_entire_packet_not_isSquare {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hpos : ∀ t : ℝ, 0 < (f t).re)
    (S : Finset ℕ) (e : ℕ) (hne : S.Nonempty) (hS : ∀ n ∈ S, 2 ≤ n) :
    ¬ IsSquare (ofMeromorphic f (fun z => (hd.analyticAt z).meromorphicAt) *
      (xiElement ^ e * ∏ n ∈ S, factorElement n)) := by
  rw [← packetElement_eq]
  obtain ⟨t, _, ht⟩ := exists_realPacket_neg S e hne hS
  apply not_isSquare_plane_of_real_sign_change (hd.mul (packet_differentiable S e))
    (fun z => by simp only [Pi.mul_apply, hconj, packet_conj, map_mul]) (x := 1) (y := t)
  refine (show (f 1 * packet S e 1).re * (f t * packet S e t).re < 0 from ?_)
  have h1 : packet S e 1 = (realPacket S e 1 : ℂ) := by
    simpa using (realPacket_cast S e 1).symm
  rw [h1, ← realPacket_cast S e t]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_neg_of_pos_of_neg (mul_pos (hpos 1) (realPacket_one_pos S e hS))
    (mul_neg_of_pos_of_neg (hpos t) ht)

/-- Any base square class with no square radical twist survives the full marked union. -/
theorem not_isSquare_markedExtension_of_twists (a : K)
    (h : ∀ T : Finset ℕ, ¬ IsSquare (a * ∏ n ∈ T, radicand n)) :
    ¬ IsSquare (algebraMap K markedExtension a) := by
  rintro ⟨r, hr⟩
  have hrΩ : (r : Ω) * r = algebraMap K Ω a := by
    have he := congrArg (fun x : markedExtension => (x : Ω)) hr
    exact he.symm
  obtain ⟨k, hk⟩ := (Subfield.mem_iSup_of_directed stage_mono.directed_le).mp r.property
  let C := independentTower base root k (by norm_num : (2 : Ω) ≠ 0)
    (fun n _ => root_sq_mem_base n) (fun T _ hT => root_radicands_independent T hT)
  have hb : C.M 0 = base := radicalStage_zero base root
  have hi : ∀ T : Finset ℕ, T ⊆ Finset.range k → T.Nonempty →
      ¬ IsSqIn (C.M 0) (∏ n ∈ T, C.d n) := by
    intro T _ hT
    rw [hb]
    exact root_radicands_independent T hT
  obtain ⟨T, _, hT⟩ := C.exists_twist_isSq (by norm_num) hi k le_rfl
    (algebraMap K Ω a) (by rw [hb]; exact RingHom.mem_fieldRange_self _ _) ⟨r, hk, hrΩ.symm⟩
  rw [hb] at hT
  change IsSqIn base (algebraMap K Ω a * ∏ n ∈ T, root n * root n) at hT
  simp_rw [root_sq] at hT
  rw [← map_prod, ← map_mul, isSqIn_base_iff] at hT
  exact h T hT


theorem positive_entire_radicand_twist_not_isSquare {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hconj : ∀ z, f (conj z) = conj (f z)) (hpos : ∀ t : ℝ, 0 < (f t).re)
    (T : Finset ℕ) (hne : T.Nonempty) :
    ¬ IsSquare (ofMeromorphic f (fun z => (hd.analyticAt z).meromorphicAt) *
      ∏ n ∈ T, radicand n) := by
  rw [prod_radicand]
  have hp := positive_entire_packet_not_isSquare hd hconj hpos
    (T.image (fun n => n + 2)) T.card (hne.image _) (by
      intro n hn
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn
      omega)
  rw [Finset.prod_image] at hp
  · exact hp
  · intro a _ b _ hab
    dsimp at hab
    omega

theorem augmentationElement_not_isSquare_markedExtension {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (algebraMap K markedExtension (augmentationElement n)) := by
  apply not_isSquare_markedExtension_of_twists
  intro T
  by_cases ht : T.Nonempty
  · exact positive_entire_radicand_twist_not_isSquare (augmentationFactor_differentiable n)
      (augmentationFactor_conj n) (augmentationFactor_real_pos n) T ht
  · simpa [Finset.not_nonempty_iff_eq_empty.mp ht] using augmentationElement_not_isSquare hn

theorem xi_mul_augmentationElement_not_isSquare_markedExtension (n : ℕ) :
    ¬ IsSquare (algebraMap K markedExtension xiElement *
      algebraMap K markedExtension (augmentationElement n)) := by
  rw [← map_mul]
  apply not_isSquare_markedExtension_of_twists
  intro T
  by_cases ht : T.Nonempty
  · have hd := xi_differentiable.mul (augmentationFactor_differentiable n)
    apply positive_entire_radicand_twist_not_isSquare hd
      (fun z => by simp only [Pi.mul_apply, xi_conj, augmentationFactor_conj, map_mul])
      (fun t => ?_) T ht
    simp only [Pi.mul_apply, Complex.mul_re, augmentationFactor_real_im, mul_zero, sub_zero]
    exact mul_pos (xi_real_pos t) (augmentationFactor_real_pos n t)
  · simpa [Finset.not_nonempty_iff_eq_empty.mp ht] using xi_mul_augmentationElement_not_isSquare n

theorem augmentationElement_eq_two_sub_factor (n : ℕ) :
    augmentationElement n = 2 - factorElement n := by
  apply MeromorphicPlane.germ_injective
  rfl

theorem augmentationElement_map_eq_sourceLambda (n : ℕ) :
    algebraMap K Marked (augmentationElement (n + 2)) = 1 + sourceParameter n := by
  rw [augmentationElement_eq_two_sub_factor, map_sub, map_ofNat]
  change 2 - factorMarked n = 1 + sourceParameter n
  have h := sourceParameter_add_factor n
  linear_combination -h

theorem sourceLambda_not_isSquare (n : ℕ) : ¬ IsSquare (1 + sourceParameter n) := by
  rw [← augmentationElement_map_eq_sourceLambda]
  exact augmentationElement_not_isSquare_markedExtension (by omega)

theorem xiMarked_mul_sourceLambda_not_isSquare (n : ℕ) :
    ¬ IsSquare (xiMarked * (1 + sourceParameter n)) := by
  rw [← augmentationElement_map_eq_sourceLambda]
  exact xi_mul_augmentationElement_not_isSquare_markedExtension (n + 2)

end RHTower.XiGlobalKummer
