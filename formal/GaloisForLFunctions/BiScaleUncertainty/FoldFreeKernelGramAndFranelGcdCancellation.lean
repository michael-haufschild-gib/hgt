import GaloisForLFunctions.RHTower.FermiNymanDyadicFoldGeometry
import GaloisForLFunctions.RHTower.CenteredFractCorrelation
import GaloisForLFunctions.BiScaleUncertainty.ProducerConsumerDualityAndNymanBeurlingBridge

/-!
# Pillar XXIX: Fold-Free Kernel Gram Decomposition & Franel GCD Sawtooth Cancellation

This module develops **Direction 1** beyond fixed log-Möbius coefficients:
1. **Explicit Fold-Free Generators in $\ker P$ (`foldFreeFermiGen`):**
   Every alternating Fermi–Nyman generator $\varphi_{a+1}(t) = \{1/((a+1)t)\} - 2\{1/(2(a+1)t)\}$
   has top-octave dyadic fold $(P\varphi_{a+1})(u) = -\frac{1}{(a+1)u}$. Subtracting its exact
   projection onto the canonical self-similar profile
   $s_0(t) = \operatorname{selfSimilarExtension}(u \mapsto u^{-1})$ (which satisfies $\|s_0\|_{L^2(0,1]}^2 = 2$
   and $(Ps_0)(u) = 2/u$) produces the **fold-free generator**
   $$\tilde{\varphi}_{a+1}(t) := \varphi_{a+1}(t) + \frac{1}{2(a+1)} s_0(t) \in \ker P.$$
   We prove unconditionally (with **zero hypotheses**) that $\tilde{\varphi}_{a+1}$ has vanishing
   dyadic fold on $(1/2, 1]$ and is strictly orthogonal to $s_0$ in $L^2(0,1]$.
2. **Exact Orthogonal Pythagoras Decomposition Across $L^2(0,1] = \ker P \oplus \mathbb{C}s_0$:**
   For ANY finite coefficient vector `c : Fin n → ℂ` and integer scale vector `a : Fin n → ℕ`, the
   full Haar approximation error splits **identically** (improving the fold–Cauchy–Schwarz lower
   bound `dyadicHaar_approximation_harmonic_penalty` to an exact orthogonal identity) into its
   $\ker P$ fold-free residual energy plus the one-dimensional self-similar harmonic shadow:
   $$\int_0^1 \left\|\operatorname{dyadicHaar}(t) - \sum_j c_j \varphi_{a_j+1}(t)\right\|^2 dt
     = \int_0^1 \left\|\operatorname{dyadicHaar}(t) - \sum_j c_j \tilde{\varphi}_{a_j+1}(t)\right\|^2 dt
       + \frac{1}{2}\left\|\sum_j \frac{c_j}{a_j+1}\right\|^2.$$
   Likewise, the generator Gram energy and pairwise Hermitian Gram matrix satisfy
   $$\langle \tilde{\varphi}_{a+1}, \tilde{\varphi}_{b+1} \rangle_{L^2(0,1]}
     = \langle \varphi_{a+1}, \varphi_{b+1} \rangle_{L^2(0,1]} - \frac{1}{2(a+1)(b+1)}.$$
3. **Closed-Form Franel GCD Sawtooth & Alternating Fermi–Franel Gram Matrices:**
   Connecting `CenteredFractCorrelation` to `BiScaleUncertainty`, we establish the exact
   off-diagonal GCD quadratic form for arbitrary linear combinations of sawtooths $\psi((a_j+1)x)$
   and for the alternating Fermi–Franel sawtooth generators
   $\psi_{\mathrm{alt}, m}(x) = \psi(mx) - 2\psi(2mx)$, proving unconditionally:
   $$\int_0^1 \psi_{\mathrm{alt}, a+1}(x)\,\psi_{\mathrm{alt}, b+1}(x)\,dx
     = \frac{5\gcd(a+1, b+1)^2 - \gcd(a+1, 2(b+1))^2 - \gcd(2(a+1), b+1)^2}{12(a+1)(b+1)},$$
   with universal diagonal energy $\frac{1}{4}$, exact adjacent-octave orthogonality
   $\int_0^1 \psi_{\mathrm{alt}, m}(x)\,\psi_{\mathrm{alt}, 2m}(x)\,dx = 0$, and coprime
   neighbor correlation $\frac{1}{4(m+1)(m+2)}$ for odd consecutive scales.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. The Canonical Self-Similar Shadow Profile $s_0$ and Fold-Free Generators $\tilde{\varphi}_{a+1} \in \ker P$ -/

/-- The canonical self-similar shadow profile $s_0(t) = \operatorname{selfSimilarExtension}(u \mapsto u^{-1})$
on $(0, 1]$, which spans the one-dimensional self-similar shadow of the Fermi–Nyman generator family. -/
def canonicalSelfSimilar (t : ℝ) : ℂ :=
  selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t

theorem measurable_canonicalSelfSimilar : Measurable canonicalSelfSimilar :=
  measurable_selfSimilarExtension Complex.measurable_ofReal.inv

theorem integrableOn_normSq_canonicalSelfSimilar :
    IntegrableOn (fun t => ‖canonicalSelfSimilar t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  integrableOn_normSq_selfSimilarExtension_inv

theorem ae_selfSimilar_canonicalSelfSimilar :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      canonicalSelfSimilar (t / 2) = canonicalSelfSimilar t :=
  ae_selfSimilar_selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)

theorem dyadicLogMean_canonicalSelfSimilar :
    dyadicLogMean canonicalSelfSimilar = 1 :=
  dyadicLogMean_selfSimilarExtension_inv

theorem integral_normSq_canonicalSelfSimilar :
    (∫ t in Ioc (0 : ℝ) 1, ‖canonicalSelfSimilar t‖ ^ 2) = 2 :=
  integral_normSq_selfSimilarExtension_inv

theorem integral_canonicalSelfSimilar_mul_conj_self :
    (∫ t in Ioc (0 : ℝ) 1,
      canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 2 := by
  have hL : (∫ t in Ioc (0 : ℝ) 1,
      canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      ((∫ t in Ioc (0 : ℝ) 1, ‖canonicalSelfSimilar t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t) =
      ((‖canonicalSelfSimilar t‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hL, integral_normSq_canonicalSelfSimilar]
  norm_num

/-- The Haar target is strictly orthogonal to the canonical self-similar profile $s_0$ on $(0,1]$. -/
theorem integral_dyadicHaar_mul_conj_canonicalSelfSimilar :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 :=
  integral_dyadicHaar_mul_conj_of_ae_selfSimilar measurable_canonicalSelfSimilar
    integrableOn_normSq_canonicalSelfSimilar ae_selfSimilar_canonicalSelfSimilar

/-- Pairing of the alternating Fermi–Nyman generator at integer scale `a + 1` with $s_0$:
$$\int_0^1 \varphi_{a+1}(t)\,\overline{s_0(t)}\,dt = -\frac{1}{a+1}.$$ -/
theorem integral_fermiNymanGen_nat_mul_conj_canonicalSelfSimilar (a : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      -(((a + 1 : ℕ) : ℂ))⁻¹ := by
  have ha : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a)
  rw [integral_fermiNymanGen_mul_conj_of_ae_selfSimilar measurable_canonicalSelfSimilar
    integrableOn_normSq_canonicalSelfSimilar ae_selfSimilar_canonicalSelfSimilar ha,
    dyadicLogMean_canonicalSelfSimilar, map_one, mul_one]
  push_cast
  rfl

/-- The **fold-free Fermi–Nyman generator** at integer scale `a + 1` (`a : ℕ`):
$$\tilde{\varphi}_{a+1}(t) := \varphi_{a+1}(t) + \frac{1}{2(a+1)} s_0(t) \in \ker P.$$ -/
def foldFreeFermiGen (a : ℕ) (t : ℝ) : ℂ :=
  fermiNymanGen ((a + 1 : ℕ) : ℝ) t +
    ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ * canonicalSelfSimilar t

theorem measurable_foldFreeFermiGen (a : ℕ) : Measurable (foldFreeFermiGen a) :=
  (measurable_fermiNymanGen _).add (measurable_const.mul measurable_canonicalSelfSimilar)

theorem integrableOn_normSq_foldFreeFermiGen (a : ℕ) :
    IntegrableOn (fun t => ‖foldFreeFermiGen a t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have h1 : MemLp (fermiNymanGen ((a + 1 : ℕ) : ℝ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_fermiNymanGen_Ioc _
  have h2 : MemLp canonicalSelfSimilar 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm
      measurable_canonicalSelfSimilar.aestronglyMeasurable).mpr
      integrableOn_normSq_canonicalSelfSimilar
  have hsum : MemLp (foldFreeFermiGen a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    h1.add (h2.const_mul _)
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_foldFreeFermiGen a).aestronglyMeasurable).mp hsum

/-- **Unconditional Top-Octave Fold Vanishing (`dyadicFold_foldFreeFermiGen_ae_eq_zero`):**
For every `a : ℕ`, the dyadic fold of `foldFreeFermiGen a` vanishes almost everywhere on the
top octave $(1/2, 1]$, so $\tilde{\varphi}_{a+1} \in \ker P$. -/
theorem dyadicFold_foldFreeFermiGen_ae_eq_zero (a : ℕ) :
    ∀ᵐ u ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)),
      dyadicFold (foldFreeFermiGen a) u = 0 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have ha : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a)
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans (by norm_num) hu.1).ne'
  have ha0 : ((a + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  have hgen := hasSum_dyadicFold_fermiNymanGen ha hu
  have hss : HasSum (fun j : ℕ =>
      (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * canonicalSelfSimilar ((1 / 2 : ℝ) ^ j * u))
      (2 * canonicalSelfSimilar u) :=
    hasSum_dyadicFold_of_selfSimilar
      (fun t ht => selfSimilarExtension_half ht) hu
  have hcomb : HasSum (fun j : ℕ =>
      (((1 / 2 : ℝ) ^ j : ℝ) : ℂ) * foldFreeFermiGen a ((1 / 2 : ℝ) ^ j * u))
      (-(((((a + 1 : ℕ) : ℝ) * u)⁻¹ : ℝ) : ℂ) +
        ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ * (2 * canonicalSelfSimilar u)) := by
    refine (hgen.add (hss.mul_left ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹)).congr_fun fun j => ?_
    unfold foldFreeFermiGen
    ring
  rw [dyadicFold, hcomb.tsum_eq]
  have htop : canonicalSelfSimilar u = ((u : ℂ))⁻¹ :=
    selfSimilarExtension_eq_of_mem hu
  rw [htop]
  push_cast
  field_simp
  ring

/-- **Unconditional Top-Octave Fold Energy Vanishing:**
For every `a : ℕ`, the top-octave $L^2(1/2, 1]$ fold energy of `foldFreeFermiGen a` is zero. -/
theorem integral_normSq_dyadicFold_foldFreeFermiGen_eq_zero (a : ℕ) :
    (∫ u in Ioc (1 / 2 : ℝ) 1, ‖dyadicFold (foldFreeFermiGen a) u‖ ^ 2) = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [dyadicFold_foldFreeFermiGen_ae_eq_zero a] with u hu
  simp [hu]

/-- **Unconditional Orthogonality of $\tilde{\varphi}_{a+1}$ to $s_0$:**
For every `a : ℕ`, the fold-free generator `foldFreeFermiGen a` is strictly orthogonal to
`canonicalSelfSimilar` on $(0, 1]$. -/
theorem integral_foldFreeFermiGen_mul_conj_canonicalSelfSimilar (a : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      foldFreeFermiGen a t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 := by
  have h1 : IntegrableOn
      (fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (canonicalSelfSimilar t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) measurable_canonicalSelfSimilar
      (integrableOn_normSq_fermiNymanGen _) integrableOn_normSq_canonicalSelfSimilar
  have h2 : IntegrableOn
      (fun t => ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ *
        (canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)))
      (Ioc (0 : ℝ) 1) :=
    (integrableOn_mul_conj_of_sq measurable_canonicalSelfSimilar
      measurable_canonicalSelfSimilar integrableOn_normSq_canonicalSelfSimilar
      integrableOn_normSq_canonicalSelfSimilar).const_mul ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹
  have hsplit : (fun t => foldFreeFermiGen a t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (canonicalSelfSimilar t) +
        ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ *
          (canonicalSelfSimilar t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
    funext t
    unfold foldFreeFermiGen
    ring
  rw [hsplit, integral_add h1 h2, integral_fermiNymanGen_nat_mul_conj_canonicalSelfSimilar a,
    integral_const_mul, integral_canonicalSelfSimilar_mul_conj_self]
  have ha0 : ((a + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  field_simp
  ring

/-! ## §2. Exact Orthogonal Pythagoras Decomposition Across $L^2(0,1] = \ker P \oplus \mathbb{C}s_0$ -/

/-- A finite linear combination $\sum_j c_j \tilde{\varphi}_{a_j+1}$ of fold-free generators at
integer scales `a j + 1`. -/
def foldFreeCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) (t : ℝ) : ℂ :=
  ∑ j, c j * foldFreeFermiGen (a j) t

/-- A finite linear combination $\sum_j c_j \varphi_{a_j+1}$ of raw Fermi–Nyman generators at
integer scales `a j + 1`. -/
def natScaleFermiCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) (t : ℝ) : ℂ :=
  fermiNymanCombination c (fun j => ((a j + 1 : ℕ) : ℝ)) t

/-- The harmonic coefficient sum $H_{c,a} = \sum_j \frac{c_j}{a_j + 1}$ governing the
self-similar shadow of a finite generator combination. -/
def harmonicCoeffSum {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) : ℂ :=
  ∑ j, c j / ((a j + 1 : ℕ) : ℂ)

/-- Pointwise relation between `foldFreeCombination`, `natScaleFermiCombination`, and the
self-similar shadow $\frac{1}{2} H_{c,a} s_0(t)$. -/
theorem foldFreeCombination_eq_add_shadow {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) (t : ℝ) :
    foldFreeCombination c a t =
      natScaleFermiCombination c a t +
        (harmonicCoeffSum c a / 2) * canonicalSelfSimilar t := by
  unfold foldFreeCombination natScaleFermiCombination fermiNymanCombination
    harmonicCoeffSum foldFreeFermiGen
  rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have haj : ((a j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (a j))
  push_cast
  field_simp

/-- Pointwise decomposition of the Haar approximation error into its $\ker P$ fold-free residual
and its self-similar shadow:
$$\operatorname{dyadicHaar}(t) - \sum_j c_j \varphi_{a_j+1}(t)
  = \left(\operatorname{dyadicHaar}(t) - \sum_j c_j \tilde{\varphi}_{a_j+1}(t)\right)
    + \frac{1}{2}\left(\sum_j \frac{c_j}{a_j+1}\right) s_0(t).$$ -/
theorem dyadicHaar_sub_natScaleFermiCombination_eq {n : ℕ}
    (c : Fin n → ℂ) (a : Fin n → ℕ) (t : ℝ) :
    dyadicHaar t - natScaleFermiCombination c a t =
      (dyadicHaar t - foldFreeCombination c a t) +
        (harmonicCoeffSum c a / 2) * canonicalSelfSimilar t := by
  rw [foldFreeCombination_eq_add_shadow]
  ring

theorem measurable_foldFreeCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    Measurable (foldFreeCombination c a) := by
  unfold foldFreeCombination
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_foldFreeFermiGen (a j))

theorem integrableOn_normSq_foldFreeCombination {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    IntegrableOn (fun t => ‖foldFreeCombination c a t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have hmem : MemLp (foldFreeCombination c a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    unfold foldFreeCombination
    exact memLp_finsetSum Finset.univ fun j _ =>
      ((memLp_two_iff_integrable_sq_norm
        (measurable_foldFreeFermiGen (a j)).aestronglyMeasurable).mpr
        (integrableOn_normSq_foldFreeFermiGen (a j))).const_mul (c j)
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_foldFreeCombination c a).aestronglyMeasurable).mp hmem

/-- Every finite combination of fold-free generators is orthogonal to $s_0$ on $(0, 1]$. -/
theorem integral_foldFreeCombination_mul_conj_canonicalSelfSimilar
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      foldFreeCombination c a t * (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 := by
  have hrew : (fun t => foldFreeCombination c a t * (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      fun t => ∑ j, c j * (foldFreeFermiGen (a j) t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
    funext t
    unfold foldFreeCombination
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrew, integral_finsetSum _ fun j _ =>
    (integrableOn_mul_conj_of_sq (measurable_foldFreeFermiGen (a j))
      measurable_canonicalSelfSimilar (integrableOn_normSq_foldFreeFermiGen (a j))
      integrableOn_normSq_canonicalSelfSimilar).const_mul (c j)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_foldFreeFermiGen_mul_conj_canonicalSelfSimilar (a j), mul_zero]

/-- The $\ker P$ Haar residual $\operatorname{dyadicHaar} - \operatorname{foldFreeCombination} c\,a$
is strictly orthogonal to the canonical self-similar shadow $s_0$ on $(0, 1]$. -/
theorem integral_dyadicHaar_sub_foldFreeCombination_mul_conj_canonicalSelfSimilar
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      (dyadicHaar t - foldFreeCombination c a t) *
        (starRingEnd ℂ) (canonicalSelfSimilar t)) = 0 := by
  have h1 := integrableOn_mul_conj_of_sq measurable_dyadicHaar measurable_canonicalSelfSimilar
    integrableOn_normSq_dyadicHaar integrableOn_normSq_canonicalSelfSimilar
  have h2 := integrableOn_mul_conj_of_sq (measurable_foldFreeCombination c a)
    measurable_canonicalSelfSimilar (integrableOn_normSq_foldFreeCombination c a)
    integrableOn_normSq_canonicalSelfSimilar
  have hsub : (fun t => (dyadicHaar t - foldFreeCombination c a t) *
      (starRingEnd ℂ) (canonicalSelfSimilar t)) =
      fun t => dyadicHaar t * (starRingEnd ℂ) (canonicalSelfSimilar t) -
        foldFreeCombination c a t * (starRingEnd ℂ) (canonicalSelfSimilar t) := by
    funext t; ring
  rw [hsub, integral_sub h1 h2, integral_dyadicHaar_mul_conj_canonicalSelfSimilar,
    integral_foldFreeCombination_mul_conj_canonicalSelfSimilar c a, sub_zero]

/-- Complex norm-square expansion `‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * conj w).re`. -/
theorem complex_norm_add_sq_eq (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * (starRingEnd ℂ) w).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add]

/-- **Exact Orthogonal Pythagoras Decomposition of the Haar Approximation Error
(`dyadicHaar_error_eq_foldFree_error_add_harmonic_shadow`):**
For EVERY `(n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℕ)` (with **zero hypotheses**!), the $L^2(0,1]$
Haar approximation error splits identically into the $\ker P$ fold-free residual energy plus the
one-dimensional self-similar harmonic shadow $\frac{1}{2}\left\|\sum_j \frac{c_j}{a_j+1}\right\|^2$:
$$\int_0^1 \left\|\operatorname{dyadicHaar}(t) - \sum_j c_j \varphi_{a_j+1}(t)\right\|^2 dt
  = \int_0^1 \left\|\operatorname{dyadicHaar}(t) - \sum_j c_j \tilde{\varphi}_{a_j+1}(t)\right\|^2 dt
    + \frac{\|\operatorname{harmonicCoeffSum}(c, a)\|^2}{2}.$$ -/
theorem dyadicHaar_error_eq_foldFree_error_add_harmonic_shadow
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - natScaleFermiCombination c a t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - foldFreeCombination c a t‖ ^ 2) +
        ‖harmonicCoeffSum c a‖ ^ 2 / 2 := by
  set R : ℝ → ℂ := fun t => dyadicHaar t - foldFreeCombination c a t
  set α : ℂ := harmonicCoeffSum c a / 2
  set S : ℝ → ℂ := fun t => α * canonicalSelfSimilar t
  have hRm : Measurable R := measurable_dyadicHaar.sub (measurable_foldFreeCombination c a)
  have hSm : Measurable S := measurable_const.mul measurable_canonicalSelfSimilar
  have hR2 : IntegrableOn (fun t => ‖R t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_normSq_sub measurable_dyadicHaar (measurable_foldFreeCombination c a)
      integrableOn_normSq_dyadicHaar (integrableOn_normSq_foldFreeCombination c a)
  have hS2 : IntegrableOn (fun t => ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    have hrew : (fun t => ‖S t‖ ^ 2) = fun t => ‖α‖ ^ 2 * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t; simp only [S, norm_mul, mul_pow]
    rw [hrew]
    exact integrableOn_normSq_canonicalSelfSimilar.const_mul (‖α‖ ^ 2)
  have hRS_int : IntegrableOn (fun t => R t * (starRingEnd ℂ) (S t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq hRm hSm hR2 hS2
  have hRe1 : IntegrableOn (fun t => (R t * (starRingEnd ℂ) (S t)).re) (Ioc (0 : ℝ) 1) :=
    hRS_int.re
  have hRe_int : IntegrableOn (fun t => 2 * (R t * (starRingEnd ℂ) (S t)).re) (Ioc (0 : ℝ) 1) :=
    hRe1.const_mul 2
  have hRS2 : IntegrableOn (fun t => ‖R t‖ ^ 2 + ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    hR2.add hS2
  have hpt : (fun t => ‖dyadicHaar t - natScaleFermiCombination c a t‖ ^ 2) =
      fun t => (‖R t‖ ^ 2 + ‖S t‖ ^ 2) + 2 * (R t * (starRingEnd ℂ) (S t)).re := by
    funext t
    rw [dyadicHaar_sub_natScaleFermiCombination_eq c a t]
    exact complex_norm_add_sq_eq (R t) (S t)
  rw [hpt, integral_add hRS2 hRe_int, integral_add hR2 hS2]
  have hcross : (∫ t in Ioc (0 : ℝ) 1, 2 * (R t * (starRingEnd ℂ) (S t)).re) = 0 := by
    rw [integral_const_mul, ← RCLike.re_eq_complex_re, integral_re hRS_int]
    have hRS_zero : (∫ t in Ioc (0 : ℝ) 1, R t * (starRingEnd ℂ) (S t)) = 0 := by
      have hfactor : (fun t => R t * (starRingEnd ℂ) (S t)) =
          fun t => (starRingEnd ℂ) α * (R t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
        funext t
        simp only [S, map_mul]
        ring
      rw [hfactor, integral_const_mul,
        integral_dyadicHaar_sub_foldFreeCombination_mul_conj_canonicalSelfSimilar c a, mul_zero]
    rw [hRS_zero, map_zero, mul_zero]
  have hS_val : (∫ t in Ioc (0 : ℝ) 1, ‖S t‖ ^ 2) = ‖harmonicCoeffSum c a‖ ^ 2 / 2 := by
    have hrew : (fun t => ‖S t‖ ^ 2) =
        fun t => (‖harmonicCoeffSum c a‖ ^ 2 / 4) * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t
      simp only [S, α, norm_mul, norm_div, Complex.norm_ofNat, mul_pow, div_pow]
      ring
    rw [hrew, integral_const_mul, integral_normSq_canonicalSelfSimilar]
    ring
  rw [hcross, add_zero, hS_val]

/-- **Exact Orthogonal Pythagoras Decomposition of the Generator Gram Energy
(`natScaleFermiCombination_normSq_eq_foldFree_add_harmonic_shadow`):**
For EVERY `(n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℕ)` (with **zero hypotheses**!),
$$\int_0^1 \left\|\sum_j c_j \varphi_{a_j+1}(t)\right\|^2 dt
  = \int_0^1 \left\|\sum_j c_j \tilde{\varphi}_{a_j+1}(t)\right\|^2 dt
    + \frac{\|\operatorname{harmonicCoeffSum}(c, a)\|^2}{2}.$$ -/
theorem natScaleFermiCombination_normSq_eq_foldFree_add_harmonic_shadow
    {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, ‖natScaleFermiCombination c a t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, ‖foldFreeCombination c a t‖ ^ 2) +
        ‖harmonicCoeffSum c a‖ ^ 2 / 2 := by
  set F : ℝ → ℂ := foldFreeCombination c a
  set α : ℂ := -(harmonicCoeffSum c a / 2)
  set S : ℝ → ℂ := fun t => α * canonicalSelfSimilar t
  have hFm : Measurable F := measurable_foldFreeCombination c a
  have hSm : Measurable S := measurable_const.mul measurable_canonicalSelfSimilar
  have hF2 : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_normSq_foldFreeCombination c a
  have hS2 : IntegrableOn (fun t => ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
    have hrew : (fun t => ‖S t‖ ^ 2) = fun t => ‖α‖ ^ 2 * ‖canonicalSelfSimilar t‖ ^ 2 := by
      funext t; simp only [S, norm_mul, mul_pow]
    rw [hrew]
    exact integrableOn_normSq_canonicalSelfSimilar.const_mul (‖α‖ ^ 2)
  have hFS_int : IntegrableOn (fun t => F t * (starRingEnd ℂ) (S t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq hFm hSm hF2 hS2
  have hRe1 : IntegrableOn (fun t => (F t * (starRingEnd ℂ) (S t)).re) (Ioc (0 : ℝ) 1) :=
    hFS_int.re
  have hRe_int : IntegrableOn (fun t => 2 * (F t * (starRingEnd ℂ) (S t)).re) (Ioc (0 : ℝ) 1) :=
    hRe1.const_mul 2
  have hFS2 : IntegrableOn (fun t => ‖F t‖ ^ 2 + ‖S t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    hF2.add hS2
  have hpt : (fun t => ‖natScaleFermiCombination c a t‖ ^ 2) =
      fun t => (‖F t‖ ^ 2 + ‖S t‖ ^ 2) + 2 * (F t * (starRingEnd ℂ) (S t)).re := by
    funext t
    have heq : natScaleFermiCombination c a t = F t + S t := by
      simp only [F, S, α, foldFreeCombination_eq_add_shadow]
      ring
    rw [heq]
    exact complex_norm_add_sq_eq (F t) (S t)
  have hcross : (∫ t in Ioc (0 : ℝ) 1, 2 * (F t * (starRingEnd ℂ) (S t)).re) = 0 := by
    have hFS_zero : (∫ t in Ioc (0 : ℝ) 1, F t * (starRingEnd ℂ) (S t)) = 0 := by
      have hfactor : (fun t => F t * (starRingEnd ℂ) (S t)) =
          fun t => (starRingEnd ℂ) α * (F t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
        funext t
        simp only [S, map_mul]
        ring
      rw [hfactor, integral_const_mul,
        integral_foldFreeCombination_mul_conj_canonicalSelfSimilar c a, mul_zero]
    rw [integral_const_mul, ← RCLike.re_eq_complex_re, integral_re hFS_int,
      hFS_zero, map_zero, mul_zero]
  rw [hpt, integral_add hFS2 hRe_int, integral_add hF2 hS2, hcross, add_zero]
  congr 1
  have hrew : (fun t => ‖S t‖ ^ 2) =
      fun t => (‖harmonicCoeffSum c a‖ ^ 2 / 4) * ‖canonicalSelfSimilar t‖ ^ 2 := by
    funext t
    simp only [S, α, norm_neg, norm_mul, norm_div, Complex.norm_ofNat, mul_pow, div_pow]
    ring
  rw [hrew, integral_const_mul, integral_normSq_canonicalSelfSimilar]
  ring

/-- **Pairwise Hermitian Gram Matrix Identity in $\ker P$:**
For EVERY `a b : ℕ` (with **zero hypotheses**!), the inner product of the fold-free generators
$\tilde{\varphi}_{a+1}$ and $\tilde{\varphi}_{b+1}$ equals the raw generator inner product minus
the rank-one harmonic shadow $\frac{1}{2(a+1)(b+1)}$:
$$\int_0^1 \tilde{\varphi}_{a+1}(t)\,\overline{\tilde{\varphi}_{b+1}(t)}\,dt
  = \int_0^1 \varphi_{a+1}(t)\,\overline{\varphi_{b+1}(t)}\,dt
    - \frac{1}{2(a+1)(b+1)}.$$ -/
theorem integral_foldFreeFermiGen_mul_conj_eq (a b : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      foldFreeFermiGen a t * (starRingEnd ℂ) (foldFreeFermiGen b t)) =
      (∫ t in Ioc (0 : ℝ) 1,
        fermiNymanGen ((a + 1 : ℕ) : ℝ) t *
          (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) -
        ((2 * ((a + 1 : ℕ) : ℂ) * ((b + 1 : ℕ) : ℂ)))⁻¹ := by
  have h1 : IntegrableOn
      (fun t => foldFreeFermiGen a t *
        (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_foldFreeFermiGen a) (measurable_fermiNymanGen _)
      (integrableOn_normSq_foldFreeFermiGen a) (integrableOn_normSq_fermiNymanGen _)
  have h2 : IntegrableOn
      (fun t => (starRingEnd ℂ) (((2 * ((b + 1 : ℕ) : ℂ)))⁻¹) *
        (foldFreeFermiGen a t * (starRingEnd ℂ) (canonicalSelfSimilar t)))
      (Ioc (0 : ℝ) 1) :=
    (integrableOn_mul_conj_of_sq (measurable_foldFreeFermiGen a)
      measurable_canonicalSelfSimilar (integrableOn_normSq_foldFreeFermiGen a)
      integrableOn_normSq_canonicalSelfSimilar).const_mul _
  have hsplitR : (fun t => foldFreeFermiGen a t * (starRingEnd ℂ) (foldFreeFermiGen b t)) =
      fun t => foldFreeFermiGen a t * (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t) +
        (starRingEnd ℂ) (((2 * ((b + 1 : ℕ) : ℂ)))⁻¹) *
          (foldFreeFermiGen a t * (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
    funext t
    unfold foldFreeFermiGen
    simp only [map_add, map_mul]
    ring
  rw [hsplitR, integral_add h1 h2, integral_const_mul,
    integral_foldFreeFermiGen_mul_conj_canonicalSelfSimilar a, mul_zero, add_zero]
  have h3 : IntegrableOn
      (fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t *
        (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) (measurable_fermiNymanGen _)
      (integrableOn_normSq_fermiNymanGen _) (integrableOn_normSq_fermiNymanGen _)
  have h4 : IntegrableOn
      (fun t => ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ *
        (canonicalSelfSimilar t * (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)))
      (Ioc (0 : ℝ) 1) :=
    (integrableOn_mul_conj_of_sq measurable_canonicalSelfSimilar (measurable_fermiNymanGen _)
      integrableOn_normSq_canonicalSelfSimilar (integrableOn_normSq_fermiNymanGen _)).const_mul _
  have hsplitL : (fun t => foldFreeFermiGen a t *
      (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) =
      fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t *
          (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t) +
        ((2 * ((a + 1 : ℕ) : ℂ)))⁻¹ *
          (canonicalSelfSimilar t * (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) := by
    funext t
    unfold foldFreeFermiGen
    ring
  rw [hsplitL, integral_add h3 h4, integral_const_mul]
  have hconj : (∫ t in Ioc (0 : ℝ) 1,
      canonicalSelfSimilar t * (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) =
      -(((b + 1 : ℕ) : ℂ))⁻¹ := by
    have hrew : (fun t => canonicalSelfSimilar t *
        (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t)) =
        fun t => (starRingEnd ℂ) (fermiNymanGen ((b + 1 : ℕ) : ℝ) t *
          (starRingEnd ℂ) (canonicalSelfSimilar t)) := by
      funext t
      simp only [map_mul, Complex.conj_conj]
      ring
    rw [hrew, integral_conj, integral_fermiNymanGen_nat_mul_conj_canonicalSelfSimilar b,
      map_neg, map_inv₀, Complex.conj_natCast]
  rw [hconj]
  have ha0 : ((a + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  have hb0 : ((b + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b)
  field_simp
  ring

/-! ## §3. Closed-Form Franel GCD Sawtooth & Alternating Fermi–Franel Gram Matrices -/

/-- The Franel sawtooth Gram matrix entry at positive integer frequencies `a + 1` and `b + 1`:
$$G^{\mathrm{Franel}}_{a,b} := \int_0^1 \psi((a+1)x)\,\psi((b+1)x)\,dx,$$
where $\psi(y) = \{y\} - 1/2$ is `centeredFract`. -/
def franelGramEntry (a b : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    centeredFract (((a + 1 : ℕ) : ℝ) * x) * centeredFract (((b + 1 : ℕ) : ℝ) * x)

/-- **Unconditional Closed-Form Franel GCD Correlation (`franelGramEntry_eq_gcd`):**
For EVERY `a b : ℕ` (with **zero hypotheses**!),
$$\operatorname{franelGramEntry}(a, b) = \frac{\gcd(a+1, b+1)^2}{12(a+1)(b+1)}.$$ -/
theorem franelGramEntry_eq_gcd (a b : ℕ) :
    franelGramEntry a b =
      ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℝ) ^ 2 /
        (12 * ((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) :=
  integral_centeredFract_mul_mul (Nat.succ_le_succ (Nat.zero_le a))
    (Nat.succ_le_succ (Nat.zero_le b))

/-- Every diagonal Franel Gram entry equals $\frac{1}{12}$ unconditionally. -/
theorem franelGramEntry_self (a : ℕ) :
    franelGramEntry a a = 1 / 12 := by
  rw [franelGramEntry_eq_gcd, Nat.gcd_self]
  have ha0 : ((a + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  field_simp

/-- Consecutive integer scales `m + 1` and `m + 2` are coprime, so their Franel Gram correlation is
unconditionally $\frac{1}{12(m+1)(m+2)}$. -/
theorem franelGramEntry_succ (m : ℕ) :
    franelGramEntry m (m + 1) =
      1 / (12 * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) := by
  rw [franelGramEntry_eq_gcd]
  have hcop : Nat.gcd (m + 1) (m + 1 + 1) = 1 := by simp
  rw [hcop]
  push_cast
  ring

/-- A finite real linear combination of dilated centered fractional parts
$\sum_{i} c_i \psi((a_i + 1) x)$. -/
def centeredFractCombination {n : ℕ} (c : Fin n → ℝ) (a : Fin n → ℕ) (x : ℝ) : ℝ :=
  ∑ i, c i * centeredFract (((a i + 1 : ℕ) : ℝ) * x)

/-- **Unconditional Exact GCD Quadratic Form for Sawtooth Combinations
(`integral_centeredFractCombination_sq_eq_gcd_sum`):**
For EVERY `(n : ℕ) (c : Fin n → ℝ) (a : Fin n → ℕ)` (with **zero hypotheses**!),
$$\int_0^1 \left(\sum_{i} c_i\,\psi((a_i+1)x)\right)^2 dx
  = \sum_{i} \sum_{j} c_i c_j \frac{\gcd(a_i+1, a_j+1)^2}{12(a_i+1)(a_j+1)}.$$ -/
theorem integral_centeredFractCombination_sq_eq_gcd_sum
    {n : ℕ} (c : Fin n → ℝ) (a : Fin n → ℕ) :
    (∫ x in (0 : ℝ)..1, centeredFractCombination c a x ^ 2) =
      ∑ i, ∑ j, c i * c j *
        (((Nat.gcd (a i + 1) (a j + 1) : ℕ) : ℝ) ^ 2 /
          (12 * ((a i + 1 : ℕ) : ℝ) * ((a j + 1 : ℕ) : ℝ))) := by
  have hint : ∀ (i j : Fin n),
      IntervalIntegrable (fun x => (c i * c j) *
        (centeredFract (((a i + 1 : ℕ) : ℝ) * x) *
          centeredFract (((a j + 1 : ℕ) : ℝ) * x))) volume 0 1 := by
    intro i j
    have h := intervalIntegrable_centeredFract_mul
      ((a i + 1 : ℕ) : ℝ) 0 ((a j + 1 : ℕ) : ℝ) 0 0 1
    simp only [add_zero] at h
    exact h.const_mul (c i * c j)
  have hint_row : ∀ i : Fin n,
      IntervalIntegrable (fun x => ∑ j, (c i * c j) *
        (centeredFract (((a i + 1 : ℕ) : ℝ) * x) *
          centeredFract (((a j + 1 : ℕ) : ℝ) * x))) volume 0 1 := by
    intro i
    have h := IntervalIntegrable.sum Finset.univ fun j _ => hint i j
    rwa [Finset.sum_fn] at h
  have hexp : (fun x => centeredFractCombination c a x ^ 2) =
      fun x => ∑ i, ∑ j, (c i * c j) *
        (centeredFract (((a i + 1 : ℕ) : ℝ) * x) *
          centeredFract (((a j + 1 : ℕ) : ℝ) * x)) := by
    funext x
    unfold centeredFractCombination
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, intervalIntegral.integral_finsetSum fun i _ => hint_row i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, ← franelGramEntry, franelGramEntry_eq_gcd]

/-- The **alternating Fermi–Franel sawtooth generator** at positive integer frequency `a + 1`:
$$\psi_{\mathrm{alt}, a+1}(x) := \psi((a+1)x) - 2\psi(2(a+1)x).$$ -/
def altCenteredFract (a : ℕ) (x : ℝ) : ℝ :=
  centeredFract (((a + 1 : ℕ) : ℝ) * x) -
    2 * centeredFract (((2 * (a + 1) : ℕ) : ℝ) * x)

/-- The alternating Fermi–Franel Gram matrix entry on $[0, 1]$:
$$G^{\mathrm{alt}}_{a,b} := \int_0^1 \psi_{\mathrm{alt}, a+1}(x)\,\psi_{\mathrm{alt}, b+1}(x)\,dx.$$ -/
def altFranelGramEntry (a b : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, altCenteredFract a x * altCenteredFract b x

/-- **Unconditional Closed-Form Alternating Fermi–Franel GCD Gram Law
(`altFranelGramEntry_eq_gcd`):**
For EVERY `a b : ℕ` (with **zero hypotheses**!), the inner product of the alternating sawtooth
generators at scales $m = a+1$ and $m' = b+1$ is given in closed form by
$$\operatorname{altFranelGramEntry}(a, b)
  = \frac{5\gcd(a+1, b+1)^2 - \gcd(a+1, 2(b+1))^2 - \gcd(2(a+1), b+1)^2}{12(a+1)(b+1)}.$$ -/
theorem altFranelGramEntry_eq_gcd (a b : ℕ) :
    altFranelGramEntry a b =
      (5 * ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℝ) ^ 2 -
        ((Nat.gcd (a + 1) (2 * (b + 1)) : ℕ) : ℝ) ^ 2 -
        ((Nat.gcd (2 * (a + 1)) (b + 1) : ℕ) : ℝ) ^ 2) /
        (12 * ((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) := by
  set m := a + 1
  set m' := b + 1
  have hm : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le a)
  have hm' : 1 ≤ m' := Nat.succ_le_succ (Nat.zero_le b)
  have h2m : 1 ≤ 2 * m := by omega
  have h2m' : 1 ≤ 2 * m' := by omega
  have i11 : IntervalIntegrable
      (fun x => centeredFract ((m : ℝ) * x) * centeredFract ((m' : ℝ) * x)) volume 0 1 := by
    simpa using intervalIntegrable_centeredFract_mul (m : ℝ) 0 (m' : ℝ) 0 0 1
  have i12 : IntervalIntegrable
      (fun x => 2 * (centeredFract ((m : ℝ) * x) *
        centeredFract (((2 * m' : ℕ) : ℝ) * x))) volume 0 1 := by
    have h := intervalIntegrable_centeredFract_mul (m : ℝ) 0 ((2 * m' : ℕ) : ℝ) 0 0 1
    simp only [add_zero] at h
    exact h.const_mul 2
  have i21 : IntervalIntegrable
      (fun x => 2 * (centeredFract (((2 * m : ℕ) : ℝ) * x) *
        centeredFract ((m' : ℝ) * x))) volume 0 1 := by
    have h := intervalIntegrable_centeredFract_mul ((2 * m : ℕ) : ℝ) 0 (m' : ℝ) 0 0 1
    simp only [add_zero] at h
    exact h.const_mul 2
  have i22 : IntervalIntegrable
      (fun x => 4 * (centeredFract (((2 * m : ℕ) : ℝ) * x) *
        centeredFract (((2 * m' : ℕ) : ℝ) * x))) volume 0 1 := by
    have h := intervalIntegrable_centeredFract_mul
      ((2 * m : ℕ) : ℝ) 0 ((2 * m' : ℕ) : ℝ) 0 0 1
    simp only [add_zero] at h
    exact h.const_mul 4
  have hexp : (fun x => altCenteredFract a x * altCenteredFract b x) =
      fun x => ((centeredFract ((m : ℝ) * x) * centeredFract ((m' : ℝ) * x) -
          2 * (centeredFract ((m : ℝ) * x) * centeredFract (((2 * m' : ℕ) : ℝ) * x))) -
          2 * (centeredFract (((2 * m : ℕ) : ℝ) * x) * centeredFract ((m' : ℝ) * x))) +
        4 * (centeredFract (((2 * m : ℕ) : ℝ) * x) *
          centeredFract (((2 * m' : ℕ) : ℝ) * x)) := by
    funext x
    unfold altCenteredFract
    ring
  unfold altFranelGramEntry
  rw [hexp,
    intervalIntegral.integral_add ((i11.sub i12).sub i21) i22,
    intervalIntegral.integral_sub (i11.sub i12) i21,
    intervalIntegral.integral_sub i11 i12,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_centeredFract_mul_mul hm hm',
    integral_centeredFract_mul_mul hm h2m',
    integral_centeredFract_mul_mul h2m hm',
    integral_centeredFract_mul_mul h2m h2m',
    Nat.gcd_mul_left]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm'0 : (m' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp
  ring

/-- **Universal Diagonal Energy of the Alternating Fermi–Franel Sawtooth (`altFranelGramEntry_self`):**
For EVERY `a : ℕ` (with **zero hypotheses**!),
$$\int_0^1 \psi_{\mathrm{alt}, a+1}(x)^2\,dx = \frac{1}{4}.$$ -/
theorem altFranelGramEntry_self (a : ℕ) :
    altFranelGramEntry a a = 1 / 4 := by
  rw [altFranelGramEntry_eq_gcd, Nat.gcd_self]
  have h1 : Nat.gcd (a + 1) (2 * (a + 1)) = a + 1 :=
    Nat.gcd_eq_left (dvd_mul_left (a + 1) 2)
  have h2 : Nat.gcd (2 * (a + 1)) (a + 1) = a + 1 :=
    Nat.gcd_eq_right (dvd_mul_left (a + 1) 2)
  rw [h1, h2]
  have ha0 : ((a + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  field_simp
  ring

/-- **Exact Adjacent-Octave Orthogonality on Every Dyadic Coset (`altFranelGramEntry_double_eq_zero`):**
For EVERY `a : ℕ` (with **zero hypotheses**!), the alternating Fermi–Franel sawtooth at scale
$m = a + 1$ is **strictly orthogonal** on $[0, 1]$ to its dyadic double at scale $2m = 2a + 2$:
$$\int_0^1 \psi_{\mathrm{alt}, a+1}(x)\,\psi_{\mathrm{alt}, 2a+2}(x)\,dx = 0.$$ -/
theorem altFranelGramEntry_double_eq_zero (a : ℕ) :
    altFranelGramEntry a (2 * a + 1) = 0 := by
  rw [altFranelGramEntry_eq_gcd]
  have hm : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
  rw [hm]
  have h1 : Nat.gcd (a + 1) (2 * (a + 1)) = a + 1 :=
    Nat.gcd_eq_left (dvd_mul_left (a + 1) 2)
  have h2 : Nat.gcd (a + 1) (2 * (2 * (a + 1))) = a + 1 := by
    rw [← mul_assoc]
    exact Nat.gcd_eq_left (dvd_mul_left (a + 1) 4)
  have h3 : Nat.gcd (2 * (a + 1)) (2 * (a + 1)) = 2 * (a + 1) := Nat.gcd_self _
  rw [h1, h2, h3]
  push_cast
  ring

/-- **Unconditional Off-Diagonal Correlation Between Odd Scales (`altFranelGramEntry_odd_odd`):**
For EVERY `k l : ℕ` (representing odd frequencies $2k+1$ and $2l+1$, with **zero hypotheses**!),
since $\gcd(2, 2k+1) = \gcd(2, 2l+1) = 1$, the alternating Fermi–Franel correlation is
$$\operatorname{altFranelGramEntry}(2k, 2l)
  = \frac{\gcd(2k+1, 2l+1)^2}{4(2k+1)(2l+1)}.$$ -/
theorem altFranelGramEntry_odd_odd (k l : ℕ) :
    altFranelGramEntry (2 * k) (2 * l) =
      ((Nat.gcd (2 * k + 1) (2 * l + 1) : ℕ) : ℝ) ^ 2 /
        (4 * ((2 * k + 1 : ℕ) : ℝ) * ((2 * l + 1 : ℕ) : ℝ)) := by
  rw [altFranelGramEntry_eq_gcd]
  have hcop_k : Nat.Coprime 2 (2 * k + 1) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hcop_l : Nat.Coprime 2 (2 * l + 1) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have h1 : Nat.gcd (2 * k + 1) (2 * (2 * l + 1)) = Nat.gcd (2 * k + 1) (2 * l + 1) := by
    rw [Nat.gcd_comm, hcop_k.gcd_mul_left_cancel (2 * l + 1), Nat.gcd_comm]
  have h2 : Nat.gcd (2 * (2 * k + 1)) (2 * l + 1) = Nat.gcd (2 * k + 1) (2 * l + 1) :=
    hcop_l.gcd_mul_left_cancel (2 * k + 1)
  rw [h1, h2]
  have hk0 : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl0 : ((2 * l + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

end

end GaloisForLFunctions.BiScaleUncertainty
