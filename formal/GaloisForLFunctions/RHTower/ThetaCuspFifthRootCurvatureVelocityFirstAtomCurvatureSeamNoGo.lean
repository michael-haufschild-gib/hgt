import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHighSourceJets
import GaloisForLFunctions.HTGeometry.AdaptiveReservedC5SeamDefect
import Mathlib.Analysis.Calculus.Taylor

/-!
# Theta C5 center velocity: first-atom-curvature seam no-go

Proof chain under test:

`strict modular-center velocity → center C5 → fixed-action transport → CLG/TTF or Weil
polarization positivity → RH`.

The prior sufficient reduction asked for global nonnegativity of the center velocity core after
replacing actual curvature by first-atom curvature.  This module proves that premise is false:
the core vanishes through order two at the modular seam, has a strictly negative third seam jet,
and is therefore negative throughout a punctured right neighborhood of the seam.

The exact positive survivor is stronger than a bare obstruction.  The second-likelihood channel
removed by that reduction has a strictly positive third seam jet which cancels the adverse core
jet exactly.  Thus any viable C5-VP1 proof must retain this likelihood cancellation; treating the
channel merely as a discardable favorable reserve destroys the seam mechanism.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

def c5VelocityFirstAtomCurvatureExpression
    (r a b c : ℝ → ℝ) (t : ℝ) : ℝ :=
  r t * (39 * a t + t * (b t - a t ^ (2 : ℕ)) +
      5 * t ^ (2 : ℕ) * (c t - 3 * a t * b t + a t ^ (3 : ℕ))) -
    17 * t * a t ^ (2 : ℕ) - 3 * t ^ (2 : ℕ) * a t * (b t - a t ^ (2 : ℕ))

theorem c5VelocityFirstAtomCurvatureExpression_seamJetClassification
    (r a b c : ℝ → ℝ)
    (hr : ContDiffAt ℝ ∞ r 0) (ha : ContDiffAt ℝ ∞ a 0)
    (hb : ContDiffAt ℝ ∞ b 0) (hc : ContDiffAt ℝ ∞ c 0)
    (k B : ℝ)
    (hr0 : iteratedDeriv 0 r 0 = 0)
    (hr1 : iteratedDeriv 1 r 0 = 0)
    (hr2 : iteratedDeriv 2 r 0 = k)
    (ha0 : iteratedDeriv 0 a 0 = 0)
    (ha1 : iteratedDeriv 1 a 0 = k)
    (hb0 : iteratedDeriv 0 b 0 = B) :
    (∀ j < 3,
      iteratedDeriv j
        (c5VelocityFirstAtomCurvatureExpression r a b c) 0 = 0) ∧
      iteratedDeriv 3
          (c5VelocityFirstAtomCurvatureExpression r a b c) 0 =
        15 * k * (k - B) := by
  let x : ℝ → ℝ := id
  let x2 : ℝ → ℝ := fun t => x t * x t
  let a2 : ℝ → ℝ := fun t => a t * a t
  let a3 : ℝ → ℝ := fun t => a2 t * a t
  let gap : ℝ → ℝ := fun t => b t - a2 t
  let third : ℝ → ℝ := fun t => c t - 3 * (a t * b t) + a3 t
  let drive : ℝ → ℝ := fun t =>
    39 * a t + x t * gap t + 5 * (x2 t * third t)
  let tax : ℝ → ℝ := fun t =>
    17 * (x t * a2 t) + 3 * ((x2 t * a t) * gap t)
  let core : ℝ → ℝ := fun t => r t * drive t - tax t
  have hx : ContDiffAt ℝ ∞ x 0 := by
    simpa only [x] using
      (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) 0)
  have hx2 : ContDiffAt ℝ ∞ x2 0 := by
    simpa only [x2] using hx.mul hx
  have ha2 : ContDiffAt ℝ ∞ a2 0 := by
    simpa only [a2] using ha.mul ha
  have ha3 : ContDiffAt ℝ ∞ a3 0 := by
    simpa only [a3] using ha2.mul ha
  have hgap : ContDiffAt ℝ ∞ gap 0 := by
    simpa only [gap] using hb.sub ha2
  have hthird : ContDiffAt ℝ ∞ third 0 := by
    dsimp only [third]
    fun_prop
  have hdrive : ContDiffAt ℝ ∞ drive 0 := by
    dsimp only [drive]
    fun_prop
  have htax : ContDiffAt ℝ ∞ tax 0 := by
    dsimp only [tax]
    fun_prop
  have hcore : ContDiffAt ℝ ∞ core 0 := by
    dsimp only [core]
    fun_prop
  have hmul (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (j : ℕ) :
      iteratedDeriv j (fun t => f t * g t) 0 =
        realScalarJetConvolution
          (fun i => iteratedDeriv i f 0)
          (fun i => iteratedDeriv i g 0) j := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (j : ℕ) :
      iteratedDeriv j (fun t => f t + g t) 0 =
        iteratedDeriv j f 0 + iteratedDeriv j g 0 := by
    exact iteratedDeriv_add
      (hf.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
      (hg : ContDiffAt ℝ ∞ g 0) (j : ℕ) :
      iteratedDeriv j (fun t => f t - g t) 0 =
        iteratedDeriv j f 0 - iteratedDeriv j g 0 := by
    exact iteratedDeriv_sub
      (hf.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
  have hscale (z : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0) (j : ℕ) :
      iteratedDeriv j (fun t => z * f t) 0 =
        z * iteratedDeriv j f 0 := by
    exact iteratedDeriv_const_mul z
      (hf.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤)))
  have hxj (j : ℕ) : iteratedDeriv j x 0 = realScalarJetId j := by
    rcases j with _ | _ | j <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have hx2j (j : ℕ) : iteratedDeriv j x2 0 =
      realScalarJetConvolution realScalarJetId realScalarJetId j := by
    rw [show iteratedDeriv j x2 0 =
      iteratedDeriv j (fun t => x t * x t) 0 by rfl,
      hmul x x hx hx j]
    simp only [hxj]
  have ha2j (j : ℕ) : iteratedDeriv j a2 0 =
      realScalarJetConvolution
        (fun i => iteratedDeriv i a 0)
        (fun i => iteratedDeriv i a 0) j := by
    rw [show iteratedDeriv j a2 0 =
      iteratedDeriv j (fun t => a t * a t) 0 by rfl,
      hmul a a ha ha j]
  have hgapj (j : ℕ) : iteratedDeriv j gap 0 =
      iteratedDeriv j b 0 - iteratedDeriv j a2 0 := by
    exact hsub b a2 hb ha2 j
  have hxa2j (j : ℕ) : iteratedDeriv j (fun t => x t * a2 t) 0 =
      realScalarJetConvolution realScalarJetId
        (fun i => iteratedDeriv i a2 0) j := by
    rw [hmul x a2 hx ha2 j]
    simp only [hxj]
  have hx2aj (j : ℕ) : iteratedDeriv j (fun t => x2 t * a t) 0 =
      realScalarJetConvolution
        (realScalarJetConvolution realScalarJetId realScalarJetId)
        (fun i => iteratedDeriv i a 0) j := by
    rw [hmul x2 a hx2 ha j]
    simp only [hx2j]
  have hx2agapj (j : ℕ) :
      iteratedDeriv j (fun t => (x2 t * a t) * gap t) 0 =
        realScalarJetConvolution
          (fun i => iteratedDeriv i (fun t => x2 t * a t) 0)
          (fun i => iteratedDeriv i gap 0) j := by
    exact hmul (fun t => x2 t * a t) gap (hx2.mul ha) hgap j
  have hthirdj (j : ℕ) : iteratedDeriv j third 0 =
      iteratedDeriv j c 0 -
          3 * iteratedDeriv j (fun t => a t * b t) 0 +
        iteratedDeriv j a3 0 := by
    dsimp only [third]
    rw [hadd (fun t => c t - 3 * (a t * b t)) a3
      (hc.sub (contDiffAt_const.mul (ha.mul hb))) ha3 j]
    rw [hsub c (fun t => 3 * (a t * b t)) hc
      (contDiffAt_const.mul (ha.mul hb)) j]
    rw [hscale 3 (fun t => a t * b t) (ha.mul hb) j]
  have hdrivej (j : ℕ) : iteratedDeriv j drive 0 =
      39 * iteratedDeriv j a 0 +
          iteratedDeriv j (fun t => x t * gap t) 0 +
        5 * iteratedDeriv j (fun t => x2 t * third t) 0 := by
    dsimp only [drive]
    rw [hadd (fun t => 39 * a t + x t * gap t)
      (fun t => 5 * (x2 t * third t))
      ((contDiffAt_const.mul ha).add (hx.mul hgap))
      (contDiffAt_const.mul (hx2.mul hthird)) j]
    rw [hadd (fun t => 39 * a t) (fun t => x t * gap t)
      (contDiffAt_const.mul ha) (hx.mul hgap) j]
    rw [hscale 39 a ha j,
      hscale 5 (fun t => x2 t * third t) (hx2.mul hthird) j]
  have htaxj (j : ℕ) : iteratedDeriv j tax 0 =
      17 * iteratedDeriv j (fun t => x t * a2 t) 0 +
        3 * iteratedDeriv j (fun t => (x2 t * a t) * gap t) 0 := by
    dsimp only [tax]
    rw [hadd (fun t => 17 * (x t * a2 t))
      (fun t => 3 * ((x2 t * a t) * gap t))
      (contDiffAt_const.mul (hx.mul ha2))
      (contDiffAt_const.mul ((hx2.mul ha).mul hgap)) j]
    rw [hscale 17 (fun t => x t * a2 t) (hx.mul ha2) j,
      hscale 3 (fun t => (x2 t * a t) * gap t)
        ((hx2.mul ha).mul hgap) j]
  have hcorej (j : ℕ) : iteratedDeriv j core 0 =
      iteratedDeriv j (fun t => r t * drive t) 0 - iteratedDeriv j tax 0 := by
    exact hsub (fun t => r t * drive t) tax (hr.mul hdrive) htax j
  have hdr0 : iteratedDeriv 0 drive 0 = 0 := by
    have ha0' : a 0 = 0 := by simpa only [iteratedDeriv_zero] using ha0
    simp [iteratedDeriv_zero, drive, x, x2, ha0']
  have hdr1 : iteratedDeriv 1 drive 0 = 39 * k + B := by
    rw [hdrivej 1]
    rw [hmul x gap hx hgap 1, hmul x2 third hx2 hthird 1]
    norm_num [realScalarJetConvolution, realScalarJetId, hxj, hx2j,
      hgapj, hthirdj, ha2j, Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0]
  have htax0 : iteratedDeriv 0 tax 0 = 0 := by
    have ha0' : a 0 = 0 := by simpa only [iteratedDeriv_zero] using ha0
    simp [iteratedDeriv_zero, tax, x, x2, a2, ha0']
  have htax1 : iteratedDeriv 1 tax 0 = 0 := by
    rw [htaxj 1]
    rw [hxa2j, hx2agapj]
    norm_num [realScalarJetConvolution, realScalarJetId, hxj, hx2j,
      ha2j, hgapj, hx2aj, Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0]
  have htax2 : iteratedDeriv 2 tax 0 = 0 := by
    rw [htaxj 2]
    rw [hxa2j, hx2agapj]
    norm_num [realScalarJetConvolution, realScalarJetId, hxj, hx2j,
      ha2j, hgapj, hx2aj, Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0]
  have htax3 : iteratedDeriv 3 tax 0 = 102 * k ^ (2 : ℕ) + 18 * k * B := by
    rw [htaxj 3]
    rw [hxa2j, hx2agapj]
    norm_num [realScalarJetConvolution, realScalarJetId, hxj, hx2j,
      ha2j, hgapj, hx2aj, Finset.sum_range_succ, Nat.choose, ha0, ha1, hb0]
    ring
  have hcore0 : iteratedDeriv 0 core 0 = 0 := by
    rw [hcorej 0, hmul r drive hr hdrive 0]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hr0, hdr0, htax0]
  have hcore1 : iteratedDeriv 1 core 0 = 0 := by
    rw [hcorej 1, hmul r drive hr hdrive 1]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hr0, hr1, hdr0, htax1]
  have hcore2 : iteratedDeriv 2 core 0 = 0 := by
    rw [hcorej 2, hmul r drive hr hdrive 2]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hr0, hr1, hdr0, htax2]
  have hcore3 : iteratedDeriv 3 core 0 = 15 * k * (k - B) := by
    rw [hcorej 3, hmul r drive hr hdrive 3]
    norm_num [realScalarJetConvolution, Finset.sum_range_succ, Nat.choose,
      hr0, hr1, hr2, hdr0, hdr1, htax3]
    ring
  have hsame : core = c5VelocityFirstAtomCurvatureExpression r a b c := by
    funext t
    dsimp only [core, drive, tax, gap, third, a2, a3, x, x2]
    unfold c5VelocityFirstAtomCurvatureExpression
    simp only [id_eq]
    ring
  rw [← hsame]
  exact ⟨fun j hj => by interval_cases j <;> assumption, hcore3⟩

end

end HTGeometry

open Set Filter Topology

namespace RHTower

noncomputable section

open HTGeometry

private def thetaCuspC5VelocityRadius (t : ℝ) : ℝ :=
  Real.exp (thetaCuspReflectedLogAction 0 t) - 1

private theorem contDiffAt_top_thetaCuspC5VelocityRadius (t : ℝ) :
    ContDiffAt ℝ ∞ thetaCuspC5VelocityRadius t := by
  have hargp : ContDiffAt ℝ ∞ (fun x : ℝ => 0 + x) t :=
    contDiffAt_const.add contDiffAt_id
  have hargm : ContDiffAt ℝ ∞ (fun x : ℝ => 0 - x) t :=
    contDiffAt_const.sub contDiffAt_id
  have hp : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (0 + x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargp
  have hm : ContDiffAt ℝ ∞
      (fun x => thetaCuspLogSource (0 - x)) t :=
    contDiff_thetaCuspLogSource.contDiffAt.comp t hargm
  unfold thetaCuspC5VelocityRadius thetaCuspReflectedLogAction
  fun_prop

private theorem contDiffAt_top_thetaCuspReflectedLogJetOne_zero (t : ℝ) :
    ContDiffAt ℝ ∞ (thetaCuspReflectedLogJetOne 0) t := by
  unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
  have h1 := HTGeometry.contDiff_top_iteratedDeriv_real
    thetaCuspLogSource contDiff_thetaCuspLogSource 1
  fun_prop

private theorem contDiffAt_top_two_thetaCuspBornWittenLogCurvature_one
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (fun x => 2 * thetaCuspBornWittenLogCurvature 1 x) t := by
  have hq : thetaCuspBornWittenWeight 1 t ≠ 0 :=
    (thetaCuspBornWittenWeight_pos
      (n := 1) (by norm_num) ht).ne'
  have hs : ContDiffAt ℝ ∞ (thetaCuspMorseScale 1) t := by
    unfold thetaCuspMorseScale
    fun_prop
  have hqd : ContDiffAt ℝ ∞ (thetaCuspBornWittenWeight 1) t := by
    unfold thetaCuspBornWittenWeight thetaCuspMorseSuperpotential
    fun_prop
  have hfrac : ContDiffAt ℝ ∞
      (fun x => 3 * thetaCuspMorseScale 1 x /
        thetaCuspBornWittenWeight 1 x ^ (2 : ℕ)) t := by
    exact (contDiffAt_const.mul hs).div (hqd.pow 2) (pow_ne_zero 2 hq)
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
  fun_prop

private theorem contDiffAt_top_neg_two_thetaCuspFirstAtomLogJetThree
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (fun x => -2 * thetaCuspFirstAtomLogJetThree x) t := by
  have hq : thetaCuspBornWittenWeight 1 t ≠ 0 :=
    (thetaCuspBornWittenWeight_pos
      (n := 1) (by norm_num) ht).ne'
  have hqd : ContDiffAt ℝ ∞ (thetaCuspBornWittenWeight 1) t := by
    unfold thetaCuspBornWittenWeight thetaCuspMorseSuperpotential
      thetaCuspMorseScale
    fun_prop
  have hq2 : ContDiffAt ℝ ∞
      (fun x => (6 : ℝ) / thetaCuspBornWittenWeight 1 x ^ (2 : ℕ)) t := by
    exact contDiffAt_const.div (hqd.pow 2) (pow_ne_zero 2 hq)
  have hq3 : ContDiffAt ℝ ∞
      (fun x => (18 : ℝ) / thetaCuspBornWittenWeight 1 x ^ (3 : ℕ)) t := by
    exact contDiffAt_const.div (hqd.pow 3) (pow_ne_zero 3 hq)
  have hleft : ContDiffAt ℝ ∞
      (fun x => 2 * thetaCuspBornWittenWeight 1 x + 3) t := by
    fun_prop
  have hright : ContDiffAt ℝ ∞
      (fun x => 4 - 6 / thetaCuspBornWittenWeight 1 x ^ (2 : ℕ) -
        18 / thetaCuspBornWittenWeight 1 x ^ (3 : ℕ)) t :=
    (contDiffAt_const.sub hq2).sub hq3
  have hprod := hleft.mul hright
  have hscaled : ContDiffAt ℝ ∞
      (fun x => 2 * ((2 * thetaCuspBornWittenWeight 1 x + 3) *
        (4 - 6 / thetaCuspBornWittenWeight 1 x ^ (2 : ℕ) -
          18 / thetaCuspBornWittenWeight 1 x ^ (3 : ℕ)))) t :=
    contDiffAt_const.mul hprod
  unfold thetaCuspFirstAtomLogJetThree thetaCuspBornWittenLogThirdDerivative
  convert hscaled using 1
  funext x
  ring

private theorem thetaCuspC5VelocityRadius_jets :
    iteratedDeriv 0 thetaCuspC5VelocityRadius 0 = 0 ∧
      iteratedDeriv 1 thetaCuspC5VelocityRadius 0 = 0 ∧
      iteratedDeriv 2 thetaCuspC5VelocityRadius 0 =
        thetaCuspReflectedLogJetTwo 0 0 := by
  constructor
  · change Real.exp (thetaCuspReflectedLogAction 0 0) - 1 = 0
    rw [show thetaCuspReflectedLogAction 0 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero]
    ring
  constructor
  · rw [iteratedDeriv_one]
    exact ((((Real.hasDerivAt_exp _).comp 0
      (hasDerivAt_thetaCuspReflectedLogAction 0 0)).sub_const 1).deriv.trans (by
        change Real.exp (thetaCuspReflectedLogAction 0 0) *
            thetaCuspReflectedLogJetOne 0 0 = 0
        rw [show thetaCuspReflectedLogJetOne 0 0 = 0 by
          unfold thetaCuspReflectedLogJetOne
          ring]
        ring))
  · have hfun : iteratedDeriv 1 thetaCuspC5VelocityRadius =
        fun t => Real.exp (thetaCuspReflectedLogAction 0 t) *
          thetaCuspReflectedLogJetOne 0 t := by
      funext t
      rw [iteratedDeriv_one]
      exact (((Real.hasDerivAt_exp _).comp t
        (hasDerivAt_thetaCuspReflectedLogAction 0 t)).sub_const 1).deriv
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, hfun]
    have h := (((Real.hasDerivAt_exp _).comp 0
      (hasDerivAt_thetaCuspReflectedLogAction 0 0)).mul
        (hasDerivAt_thetaCuspReflectedLogJetOne 0 0)).deriv
    change deriv ((Real.exp ∘ thetaCuspReflectedLogAction 0) *
      thetaCuspReflectedLogJetOne 0) 0 = thetaCuspReflectedLogJetTwo 0 0
    rw [h]
    change Real.exp (thetaCuspReflectedLogAction 0 0) *
      thetaCuspReflectedLogJetOne 0 0 * thetaCuspReflectedLogJetOne 0 0 +
        Real.exp (thetaCuspReflectedLogAction 0 0) *
          thetaCuspReflectedLogJetTwo 0 0 = thetaCuspReflectedLogJetTwo 0 0
    rw [show thetaCuspReflectedLogAction 0 0 = 0 by
      unfold thetaCuspReflectedLogAction
      ring, Real.exp_zero,
      show thetaCuspReflectedLogJetOne 0 0 = 0 by
        unfold thetaCuspReflectedLogJetOne
        ring]
    ring

private theorem iteratedDeriv_two_thetaCuspLogSource_zero_eq_factor :
    iteratedDeriv 2 thetaCuspLogSource 0 =
      -thetaCuspBornWittenLogCurvature 1 0 +
        thetaCuspLikelihoodSourceLogPartitionJetTwo 0 := by
  let f : ℝ → ℝ := iteratedDeriv 2 thetaCuspLogSource
  let g : ℝ → ℝ := fun x =>
    -thetaCuspBornWittenLogCurvature 1 x +
      thetaCuspLikelihoodSourceLogPartitionJetTwo x
  have hf : ContinuousAt f 0 := by
    have h2 := HTGeometry.contDiff_top_iteratedDeriv_real
      thetaCuspLogSource contDiff_thetaCuspLogSource 2
    exact h2.continuous.continuousAt
  have hg : ContinuousAt g 0 := by
    have hB :=
      (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) (show 0 ≤ (0 : ℝ) by norm_num)).continuousAt
    have hG :=
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
        (thetaCuspLikelihoodCoordinate_pos (show 0 ≤ (0 : ℝ) by norm_num))).continuousAt
    exact hB.neg.add hG
  have heq : f =ᶠ[𝓝[Ioi 0] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    dsimp only [f, g]
    rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
      ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx]
  have hf' : Tendsto f (𝓝[Ioi 0] 0) (𝓝 (f 0)) :=
    hf.continuousWithinAt.tendsto
  have hg' : Tendsto g (𝓝[Ioi 0] 0) (𝓝 (g 0)) :=
    hg.continuousWithinAt.tendsto
  have hfg : f 0 = g 0 := tendsto_nhds_unique (hf'.congr' heq) hg'
  simpa only [f, g] using hfg

theorem thetaCuspReflectedLogJetTwo_zero_zero_eq_likelihood :
    thetaCuspReflectedLogJetTwo 0 0 =
      2 * (thetaCuspBornWittenLogCurvature 1 0 -
        thetaCuspLikelihoodSourceLogPartitionJetTwo 0) := by
  rw [show thetaCuspReflectedLogJetTwo 0 0 =
      -2 * iteratedDeriv 2 thetaCuspLogSource 0 by
    unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
    ring]
  rw [iteratedDeriv_two_thetaCuspLogSource_zero_eq_factor]
  ring

theorem thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_seamJetClassification :
    let k := thetaCuspReflectedLogJetTwo 0 0
    let B := 2 * thetaCuspBornWittenLogCurvature 1 0
    (∀ j < 3,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 = 0) ∧
      iteratedDeriv 3 thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 =
        15 * k * (k - B) := by
  dsimp only
  rcases thetaCuspC5VelocityRadius_jets with ⟨hr0, hr1, hr2⟩
  have ha0 : iteratedDeriv 0 (thetaCuspReflectedLogJetOne 0) 0 = 0 := by
    simp [iteratedDeriv_zero, thetaCuspReflectedLogJetOne]
  have ha1 : iteratedDeriv 1 (thetaCuspReflectedLogJetOne 0) 0 =
      thetaCuspReflectedLogJetTwo 0 0 := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspReflectedLogJetOne 0 0).deriv
  have hb0 : iteratedDeriv 0
      (fun x => 2 * thetaCuspBornWittenLogCurvature 1 x) 0 =
        2 * thetaCuspBornWittenLogCurvature 1 0 := rfl
  have h := HTGeometry.c5VelocityFirstAtomCurvatureExpression_seamJetClassification
    thetaCuspC5VelocityRadius
    (thetaCuspReflectedLogJetOne 0)
    (fun x => 2 * thetaCuspBornWittenLogCurvature 1 x)
    (fun x => -2 * thetaCuspFirstAtomLogJetThree x)
    (contDiffAt_top_thetaCuspC5VelocityRadius 0)
    (contDiffAt_top_thetaCuspReflectedLogJetOne_zero 0)
    (contDiffAt_top_two_thetaCuspBornWittenLogCurvature_one (by norm_num))
    (contDiffAt_top_neg_two_thetaCuspFirstAtomLogJetThree (by norm_num))
    (thetaCuspReflectedLogJetTwo 0 0)
    (2 * thetaCuspBornWittenLogCurvature 1 0)
    hr0 hr1 hr2 ha0 ha1 hb0
  change (∀ j < 3,
      iteratedDeriv j thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 = 0) ∧
    iteratedDeriv 3 thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 =
      15 * thetaCuspReflectedLogJetTwo 0 0 *
        (thetaCuspReflectedLogJetTwo 0 0 -
          2 * thetaCuspBornWittenLogCurvature 1 0) at h
  exact h

theorem iteratedDeriv_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg :
    iteratedDeriv 3 thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 < 0 := by
  rw [thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_seamJetClassification.2]
  have hk : 0 < thetaCuspReflectedLogJetTwo 0 0 := by
    rw [thetaCuspReflectedLogJetTwo_zero]
    exact mul_pos (by norm_num) (thetaCuspLogCurvature_pos 0)
  have hG := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
    (show 0 ≤ (0 : ℝ) by norm_num)
  have hdecomp := thetaCuspReflectedLogJetTwo_zero_zero_eq_likelihood
  have hgap : thetaCuspReflectedLogJetTwo 0 0 -
      2 * thetaCuspBornWittenLogCurvature 1 0 < 0 := by
    nlinarith
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hk) hgap

private theorem contDiffAt_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ 3 thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t := by
  have hr := contDiffAt_top_thetaCuspC5VelocityRadius t
  have ha := contDiffAt_top_thetaCuspReflectedLogJetOne_zero t
  have hb := contDiffAt_top_two_thetaCuspBornWittenLogCurvature_one ht
  have hc := contDiffAt_top_neg_two_thetaCuspFirstAtomLogJetThree ht
  have hr3 : ContDiffAt ℝ 3 thetaCuspC5VelocityRadius t :=
    hr.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have ha3 : ContDiffAt ℝ 3 (thetaCuspReflectedLogJetOne 0) t :=
    ha.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have hb3 : ContDiffAt ℝ 3
      (fun x => 2 * thetaCuspBornWittenLogCurvature 1 x) t :=
    hb.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have hc3 : ContDiffAt ℝ 3
      (fun x => -2 * thetaCuspFirstAtomLogJetThree x) t :=
    hc.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  change ContDiffAt ℝ 3
    (HTGeometry.c5VelocityFirstAtomCurvatureExpression
      thetaCuspC5VelocityRadius
      (thetaCuspReflectedLogJetOne 0)
      (fun x => 2 * thetaCuspBornWittenLogCurvature 1 x)
      (fun x => -2 * thetaCuspFirstAtomLogJetThree x)) t
  unfold HTGeometry.c5VelocityFirstAtomCurvatureExpression
  fun_prop

private theorem continuousAt_iteratedDeriv_three_of_contDiffAt_three
    {f : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ 3 f x) :
    ContinuousAt (iteratedDeriv 3 f) x := by
  have hF : ContinuousAt (iteratedFDeriv ℝ 3 f) x :=
    h.continuousAt_iteratedFDeriv le_rfl
  have happ : Continuous
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ℝ) ℝ =>
        T (fun _ => 1)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => ℝ) ℝ
      (fun _ => 1)).continuous
  have hc : ContinuousAt
      (fun y => (iteratedFDeriv ℝ 3 f y) (fun _ => 1)) x :=
    happ.continuousAt.comp hF
  have hfun : iteratedDeriv 3 f =
      fun y => (iteratedFDeriv ℝ 3 f y) (fun _ => 1) := by
    funext y
    rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hfun]
  exact hc

private def c5VelocityIteratedTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_c5VelocityIteratedTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hr : 0 < r) (j : ℕ) (hj : j ≤ 2) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      c5VelocityIteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [c5VelocityIteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih (by omega)]
      simp only [c5VelocityIteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        have hj3 : ((j + 1 : ℕ) : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞) := by
          exact_mod_cast (show j + 1 ≤ 3 by omega)
        have hf' : ContDiffAt ℝ (j + 1) f x := hf.of_le hj3
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith)) hf' (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_taylor_two_zero
    {t : ℝ} (ht : 0 < t) :
    taylorWithinEval thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 2
      (uIcc 0 t) 0 t = 0 := by
  have hTaylor := taylorWithinEval_add_eq_c5VelocityIteratedTaylorShift
    (f := thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore)
    (x := 0) (r := t)
    (contDiffAt_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
      (by norm_num)) ht 2 (by norm_num)
  simpa only [zero_add] using hTaylor.trans (by
    unfold c5VelocityIteratedTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_seamJetClassification.1
      k (Finset.mem_range.mp hk)]
    simp)

/-- The stripped first-atom-curvature sufficient core is negative immediately right of seam. -/
theorem eventually_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t < 0 := by
  let f := thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
  have hf0 : ContDiffAt ℝ 3 f 0 := by
    simpa only [f] using
      contDiffAt_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
        (show 0 ≤ (0 : ℝ) by norm_num)
  have hf3 : ContinuousAt (iteratedDeriv 3 f) 0 :=
    continuousAt_iteratedDeriv_three_of_contDiffAt_three hf0
  have hneg0 : iteratedDeriv 3 f 0 < 0 := by
    simpa only [f] using
      iteratedDeriv_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg
  have hevent : {x : ℝ | iteratedDeriv 3 f x < 0} ∈ nhds 0 :=
    hf3.eventually (Iio_mem_nhds hneg0)
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht htε
  have hfOn : ContDiffOn ℝ 3 f (uIcc 0 t) := by
    rw [uIcc_of_le ht.le]
    intro x hx
    exact (contDiffAt_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
      hx.1).contDiffWithinAt
  have hTaylor : taylorWithinEval f 2 (uIcc 0 t) 0 t = 0 := by
    simpa only [f] using
      thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_taylor_two_zero ht
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := t) (x₀ := 0) (n := 2) (ne_of_lt ht) hfOn
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans htε
  have hxneg : iteratedDeriv 3 f x < 0 := hball hxball
  rw [hTaylor, sub_zero, sub_zero] at hrem
  change f t < 0
  rw [hrem]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hxneg (pow_pos ht 3))
    (by positivity)

/-- Global nonnegativity of the stripped core, the prior sufficient route to C5-VP1, is false. -/
theorem not_forall_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_nonneg :
    ¬ ∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t := by
  rcases eventually_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg with
    ⟨δ, hδ, hlocal⟩
  intro hnonneg
  let t := δ / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have htδ : t < δ := by dsimp only [t]; linarith
  exact (not_lt_of_ge (hnonneg t ht)) (hlocal t ht htδ)

/-- Universal second-likelihood correction retained by the exact C5 velocity decomposition. -/
def c5VelocitySecondLikelihoodCorrectionExpression
    (r a g : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * t * g t *
    (r t * (30 * t + 15 * t * a t - 1) + 3 * t * a t)

/-- Seam law for the correction: its first nonzero jet is exactly `30*k*G`. -/
theorem c5VelocitySecondLikelihoodCorrectionExpression_seamJetClassification
    (r a g : ℝ → ℝ)
    (hr : ContDiffAt ℝ 3 r 0) (ha : ContDiffAt ℝ 3 a 0)
    (hg : ContDiffAt ℝ 3 g 0) (k G : ℝ)
    (hr0 : iteratedDeriv 0 r 0 = 0)
    (hr1 : iteratedDeriv 1 r 0 = 0)
    (hr2 : iteratedDeriv 2 r 0 = k)
    (ha0 : iteratedDeriv 0 a 0 = 0)
    (ha1 : iteratedDeriv 1 a 0 = k)
    (hg0 : iteratedDeriv 0 g 0 = G) :
    (∀ j < 3,
      iteratedDeriv j
        (c5VelocitySecondLikelihoodCorrectionExpression r a g) 0 = 0) ∧
      iteratedDeriv 3
        (c5VelocitySecondLikelihoodCorrectionExpression r a g) 0 =
          30 * k * G := by
  let x : ℝ → ℝ := id
  let xa : ℝ → ℝ := fun t => x t * a t
  let xg : ℝ → ℝ := fun t => x t * g t
  let coeff : ℝ → ℝ := fun t => 30 * x t + 15 * xa t - 1
  let bracket : ℝ → ℝ := fun t => r t * coeff t + 3 * xa t
  let corr : ℝ → ℝ := fun t => 2 * (xg t * bracket t)
  have hx : ContDiffAt ℝ 3 x 0 := by
    simpa only [x] using (contDiffAt_id : ContDiffAt ℝ 3 (id : ℝ → ℝ) 0)
  have hxa : ContDiffAt ℝ 3 xa 0 := by simpa only [xa] using hx.mul ha
  have hxg : ContDiffAt ℝ 3 xg 0 := by simpa only [xg] using hx.mul hg
  have hcoeff : ContDiffAt ℝ 3 coeff 0 := by
    dsimp only [coeff]
    fun_prop
  have hbracket : ContDiffAt ℝ 3 bracket 0 := by
    dsimp only [bracket]
    fun_prop
  have hcorr : ContDiffAt ℝ 3 corr 0 := by
    dsimp only [corr]
    fun_prop
  have hmul (f h : ℝ → ℝ) (hf : ContDiffAt ℝ 3 f 0)
      (hh : ContDiffAt ℝ 3 h 0) (j : ℕ) (hj : j ≤ 3) :
      iteratedDeriv j (fun t => f t * h t) 0 =
        realScalarJetConvolution
          (fun i => iteratedDeriv i f 0)
          (fun i => iteratedDeriv i h 0) j := by
    exact iteratedDeriv_mul_eq_realScalarJetConvolution
      (hf.of_le (by exact_mod_cast hj)) (hh.of_le (by exact_mod_cast hj))
  have hadd (f h : ℝ → ℝ) (hf : ContDiffAt ℝ 3 f 0)
      (hh : ContDiffAt ℝ 3 h 0) (j : ℕ) (hj : j ≤ 3) :
      iteratedDeriv j (fun t => f t + h t) 0 =
        iteratedDeriv j f 0 + iteratedDeriv j h 0 := by
    exact iteratedDeriv_add
      (hf.of_le (by exact_mod_cast hj)) (hh.of_le (by exact_mod_cast hj))
  have hscale (z : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ 3 f 0)
      (j : ℕ) (hj : j ≤ 3) :
      iteratedDeriv j (fun t => z * f t) 0 = z * iteratedDeriv j f 0 := by
    exact iteratedDeriv_const_mul z (hf.of_le (by exact_mod_cast hj))
  have hxj (j : ℕ) : iteratedDeriv j x 0 = realScalarJetId j := by
    rcases j with _ | _ | j <;> simp [x, realScalarJetId, iteratedDeriv_id]
  have hxaj (j : ℕ) (hj : j ≤ 3) : iteratedDeriv j xa 0 =
      realScalarJetConvolution realScalarJetId
        (fun i => iteratedDeriv i a 0) j := by
    rw [show iteratedDeriv j xa 0 =
      iteratedDeriv j (fun t => x t * a t) 0 by rfl,
      hmul x a hx ha j hj]
    simp only [hxj]
  have hxgj (j : ℕ) (hj : j ≤ 3) : iteratedDeriv j xg 0 =
      realScalarJetConvolution realScalarJetId
        (fun i => iteratedDeriv i g 0) j := by
    rw [show iteratedDeriv j xg 0 =
      iteratedDeriv j (fun t => x t * g t) 0 by rfl,
      hmul x g hx hg j hj]
    simp only [hxj]
  have hcoeff0 : iteratedDeriv 0 coeff 0 = -1 := by
    have ha0' : a 0 = 0 := by simpa only [iteratedDeriv_zero] using ha0
    simp [iteratedDeriv_zero, coeff, x, xa, ha0']
  have hbracketj (j : ℕ) (hj : j ≤ 3) : iteratedDeriv j bracket 0 =
      iteratedDeriv j (fun t => r t * coeff t) 0 +
        3 * iteratedDeriv j xa 0 := by
    dsimp only [bracket]
    rw [hadd (fun t => r t * coeff t) (fun t => 3 * xa t)
      (hr.mul hcoeff) (contDiffAt_const.mul hxa) j hj,
      hscale 3 xa hxa j hj]
  have hcorrj (j : ℕ) (hj : j ≤ 3) : iteratedDeriv j corr 0 =
      2 * iteratedDeriv j (fun t => xg t * bracket t) 0 := by
    dsimp only [corr]
    exact hscale 2 (fun t => xg t * bracket t) (hxg.mul hbracket) j hj
  have hbr0 : iteratedDeriv 0 bracket 0 = 0 := by
    rw [hbracketj 0 (by norm_num), hmul r coeff hr hcoeff 0 (by norm_num),
      hxaj 0 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, ha0]
  have hbr1 : iteratedDeriv 1 bracket 0 = 0 := by
    rw [hbracketj 1 (by norm_num), hmul r coeff hr hcoeff 1 (by norm_num),
      hxaj 1 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1, ha0]
  have hbr2 : iteratedDeriv 2 bracket 0 = 5 * k := by
    rw [hbracketj 2 (by norm_num), hmul r coeff hr hcoeff 2 (by norm_num),
      hxaj 2 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hr0, hr1, hr2, ha0, ha1, hcoeff0]
    ring
  have hcorr0 : iteratedDeriv 0 corr 0 = 0 := by
    rw [hcorrj 0 (by norm_num), hmul xg bracket hxg hbracket 0 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hxgj, hg0, hbr0]
  have hcorr1 : iteratedDeriv 1 corr 0 = 0 := by
    rw [hcorrj 1 (by norm_num), hmul xg bracket hxg hbracket 1 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hxgj, hg0, hbr0, hbr1]
  have hcorr2 : iteratedDeriv 2 corr 0 = 0 := by
    rw [hcorrj 2 (by norm_num), hmul xg bracket hxg hbracket 2 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hxgj, hg0, hbr0, hbr1]
  have hcorr3 : iteratedDeriv 3 corr 0 = 30 * k * G := by
    rw [hcorrj 3 (by norm_num), hmul xg bracket hxg hbracket 3 (by norm_num)]
    norm_num [realScalarJetConvolution, realScalarJetId,
      Finset.sum_range_succ, Nat.choose, hxgj, hg0, hbr0, hbr1, hbr2]
    ring
  have hsame : corr = c5VelocitySecondLikelihoodCorrectionExpression r a g := by
    funext t
    dsimp only [corr, xg, bracket, coeff, xa, x]
    unfold c5VelocitySecondLikelihoodCorrectionExpression
    simp only [id_eq]
    ring
  rw [← hsame]
  exact ⟨fun j hj => by interval_cases j <;> assumption, hcorr3⟩

private theorem contDiffAt_succ_real_of_eventually_hasDerivAt_c5Velocity
    {f g : ℝ → ℝ} {u : ℝ} {n : ℕ}
    (hfg : ∀ᶠ x in nhds u, HasDerivAt f (g x) x)
    (hg : ContDiffAt ℝ n g u) :
    ContDiffAt ℝ (n + 1) f u := by
  rw [contDiffAt_succ_iff_hasFDerivAt]
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨fun x => L (g x), ?_, ?_⟩
  · refine ⟨{x | HasDerivAt f (g x) x}, hfg, fun x hx => ?_⟩
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa [L] using hx
  · have hL : ContDiffAt ℝ n L (g u) :=
      (L.contDiff : ContDiff ℝ n L).contDiffAt
    exact hL.comp u hg

private theorem contDiffAt_three_thetaCuspLikelihoodSourceLogPartitionJetTwo_zero :
    ContDiffAt ℝ 3 thetaCuspLikelihoodSourceLogPartitionJetTwo 0 := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (show 0 ≤ (0 : ℝ) by norm_num)
  have hcoord : ContinuousAt thetaCuspLikelihoodCoordinate 0 :=
    (hasDerivAt_thetaCuspLikelihoodCoordinate 0).continuousAt
  have hevent : {x : ℝ | 0 < thetaCuspLikelihoodCoordinate x} ∈ nhds 0 :=
    hcoord.eventually (Ioi_mem_nhds hB0)
  have h5 : ContDiffAt ℝ 0 thetaCuspLikelihoodSourceLogPartitionJetFive 0 := by
    rw [contDiffAt_zero]
    refine ⟨{x : ℝ | 0 < thetaCuspLikelihoodCoordinate x}, hevent, ?_⟩
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFive hx).continuousAt.continuousWithinAt
  have h4 : ContDiffAt ℝ 1 thetaCuspLikelihoodSourceLogPartitionJetFour 0 := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_c5Velocity
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hx
    · exact h5
  have h3 : ContDiffAt ℝ 2 thetaCuspLikelihoodSourceLogPartitionJetThree 0 := by
    apply contDiffAt_succ_real_of_eventually_hasDerivAt_c5Velocity
    · filter_upwards [hevent] with x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hx
    · exact h4
  apply contDiffAt_succ_real_of_eventually_hasDerivAt_c5Velocity
  · filter_upwards [hevent] with x hx
    exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hx
  · exact h3

/-- Concrete likelihood correction in exact center-velocity coordinates. -/
def thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection (t : ℝ) : ℝ :=
  c5VelocitySecondLikelihoodCorrectionExpression
    thetaCuspC5VelocityRadius (thetaCuspReflectedLogJetOne 0)
    thetaCuspLikelihoodSourceLogPartitionJetTwo t

/-- On the physical ray this is literally the channel removed from the stripped core. -/
theorem thetaCuspCenterFifthRootVelocityMasterReservedCore_eq_firstAtomCurvature_add_correction
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityMasterReservedCore t =
      thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t +
        thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection t := by
  rw [thetaCuspCenterFifthRootVelocityMasterReservedCore_eq_firstAtomCurvature_add ht]
  rfl

/-- Exact seam classification of the source-specific second-likelihood correction. -/
theorem thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection_seamJetClassification :
    let k := thetaCuspReflectedLogJetTwo 0 0
    let G := thetaCuspLikelihoodSourceLogPartitionJetTwo 0
    (∀ j < 3,
      iteratedDeriv j thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 = 0) ∧
      iteratedDeriv 3 thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 =
        30 * k * G := by
  dsimp only
  rcases thetaCuspC5VelocityRadius_jets with ⟨hr0, hr1, hr2⟩
  have ha0 : iteratedDeriv 0 (thetaCuspReflectedLogJetOne 0) 0 = 0 := by
    simp [iteratedDeriv_zero, thetaCuspReflectedLogJetOne]
  have ha1 : iteratedDeriv 1 (thetaCuspReflectedLogJetOne 0) 0 =
      thetaCuspReflectedLogJetTwo 0 0 := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_thetaCuspReflectedLogJetOne 0 0).deriv
  have hg0 : iteratedDeriv 0 thetaCuspLikelihoodSourceLogPartitionJetTwo 0 =
      thetaCuspLikelihoodSourceLogPartitionJetTwo 0 := rfl
  have hr3 : ContDiffAt ℝ 3 thetaCuspC5VelocityRadius 0 :=
    (contDiffAt_top_thetaCuspC5VelocityRadius 0).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have ha3 : ContDiffAt ℝ 3 (thetaCuspReflectedLogJetOne 0) 0 :=
    (contDiffAt_top_thetaCuspReflectedLogJetOne_zero 0).of_le
      (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have h := c5VelocitySecondLikelihoodCorrectionExpression_seamJetClassification
    thetaCuspC5VelocityRadius (thetaCuspReflectedLogJetOne 0)
    thetaCuspLikelihoodSourceLogPartitionJetTwo hr3 ha3
    contDiffAt_three_thetaCuspLikelihoodSourceLogPartitionJetTwo_zero
    (thetaCuspReflectedLogJetTwo 0 0)
    (thetaCuspLikelihoodSourceLogPartitionJetTwo 0)
    hr0 hr1 hr2 ha0 ha1 hg0
  change (∀ j < 3,
      iteratedDeriv j thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 = 0) ∧
    iteratedDeriv 3 thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 =
      30 * thetaCuspReflectedLogJetTwo 0 0 *
        thetaCuspLikelihoodSourceLogPartitionJetTwo 0 at h
  exact h

/-- The likelihood correction has a strictly positive cubic seam jet. -/
theorem iteratedDeriv_three_thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection_pos :
    0 < iteratedDeriv 3 thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 := by
  rw [thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection_seamJetClassification.2]
  have hk : 0 < thetaCuspReflectedLogJetTwo 0 0 := by
    rw [thetaCuspReflectedLogJetTwo_zero]
    exact mul_pos (by norm_num) (thetaCuspLogCurvature_pos 0)
  have hG := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
    (show 0 ≤ (0 : ℝ) by norm_num)
  positivity

/-- Seam-essential cancellation: the removed likelihood channel exactly cancels the adverse
cubic jet of the stripped first-atom-curvature core. -/
theorem iteratedDeriv_three_thetaCuspCenterFirstAtomCore_add_secondLikelihoodCorrection_eq_zero :
    iteratedDeriv 3 thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore 0 +
      iteratedDeriv 3 thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection 0 = 0 := by
  rw [thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_seamJetClassification.2,
    thetaCuspCenterFifthRootVelocitySecondLikelihoodCorrection_seamJetClassification.2,
    thetaCuspReflectedLogJetTwo_zero_zero_eq_likelihood]
  ring

end

end RHTower
