import GaloisForLFunctions.RHTower.ChiRamanujanUniformLabelSource
import GaloisForLFunctions.RHTower.ChiRamanujanUniformPoleControl

/-!
# Global axes envelope for the original growing source

For every fixed positive pair of logarithmic Mellin lines, the COMPLETE
original source is bounded by a polynomial frequency weight times two
inverse-square axis profiles, uniformly in all real frequency pairs.
Both original growing cofactors and every allowed label collision remain.

The exact uniform labelled factor bound, all-frequency finite Euler pole
comparison and the filled zeta residue factor pay every factor. The bound
supplies domination against fixed Schwartz tests; signed cancellation and
transfer to the actual moving physical profile are separate obligations.
-/

noncomputable section
open Filter Set Metric
open scoped BigOperators Topology
namespace RHTower.BAGTrace

private def movingPoint (ρ t : ℝ) (N : ℕ) : ℂ :=
  ((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I

private theorem movingPoint_re (ρ t : ℝ) (N : ℕ) :
    (movingPoint ρ t N).re=ρ/Real.log N := by
  simp only [movingPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,mul_zero,zero_mul,sub_self,add_zero]

private theorem movingPoint_im (ρ t : ℝ) (N : ℕ) :
    (movingPoint ρ t N).im=t := by
  simp only [movingPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add]

private def poleSize (N : ℕ) (t : ℝ) : ℝ := 1/Real.log N+|t|

private theorem poleSize_pos {N : ℕ} (hN : 2 ≤ N) (t : ℝ) : 0<poleSize N t := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  dsimp [poleSize]
  positivity

private theorem pole_norm_comparison {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖movingPoint 1 t N‖ ≤ poleSize N t ∧ poleSize N t ≤ 2*‖movingPoint 1 t N‖ := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have he : 0 ≤ 1/Real.log N := by positivity
  have hre := Complex.abs_re_le_norm (movingPoint 1 t N)
  have him := Complex.abs_im_le_norm (movingPoint 1 t N)
  rw [movingPoint_re,abs_of_nonneg he] at hre
  rw [movingPoint_im] at him
  constructor
  · have h := norm_add_le (((1/Real.log N : ℝ) : ℂ)) ((t : ℂ)*Complex.I)
    simpa only [movingPoint,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,
      mul_one,abs_of_nonneg he,poleSize] using h
  · dsimp [poleSize]; linarith

private theorem zeta_pole_bound (ρ : {r : ℝ // 0<r}) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      ‖riemannZeta (1+movingPoint ρ t N)‖*poleSize N t ≤ B*(1+|t|)^9 := by
  obtain ⟨c,hc,M,hM,hres⟩ := exists_residue_global_polynomial_disks
  let K : ℝ := 1/(ρ : ℝ)+1
  have hK : 0<K := by dsimp [K]; have := ρ.property; positivity
  refine ⟨K*M,mul_pos hK hM,?_⟩
  have hρ := (tendsto_drift_zero (ρ : ℝ)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hρ,eventually_ge_atTop 2] with N hNρ hN
  intro t
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hρL : 0<(ρ : ℝ)/Real.log N := div_pos ρ.property hL
  have hh := hres (1+(ρ : ℝ)/Real.log N) ⟨by linarith,by linarith⟩ t
    (((1+(ρ : ℝ)/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)
    (by simpa only [mem_closedBall,dist_self] using
      (show (0 : ℝ) ≤ c/(1+|t|)^9 from div_nonneg hc.1.le (by positivity)))
  have hs : (((1+(ρ : ℝ)/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I)=
      1+movingPoint ρ t N := by dsimp [movingPoint]; push_cast; ring
  rw [hs] at hh
  have hsne : 1+movingPoint ρ t N ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    rw [Complex.add_re,Complex.one_re,movingPoint_re] at hre
    linarith
  have hfactor : zetaResidueFactor (1+movingPoint ρ t N)=
      movingPoint ρ t N*riemannZeta (1+movingPoint ρ t N) := by
    rw [zetaResidueFactor_of_ne hsne]
    congr 1
    ring
  have hnorm : ‖movingPoint ρ t N‖*‖riemannZeta (1+movingPoint ρ t N)‖ ≤ M*(1+|t|)^9 := by
    simpa only [hfactor,norm_mul] using hh.2.1
  have hre := Complex.abs_re_le_norm (movingPoint ρ t N)
  rw [movingPoint_re,abs_of_pos hρL] at hre
  have him := Complex.abs_im_le_norm (movingPoint ρ t N)
  rw [movingPoint_im] at him
  have heps : 1/Real.log N ≤ ‖movingPoint ρ t N‖/(ρ : ℝ) := by
    apply (le_div_iff₀ ρ.property).mpr
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hre
  have hpole : poleSize N t ≤ K*‖movingPoint ρ t N‖ := by
    dsimp [poleSize,K]
    calc 1/Real.log N+|t| ≤ ‖movingPoint ρ t N‖/(ρ : ℝ)+‖movingPoint ρ t N‖ := by linarith
         _ = _ := by ring
  calc ‖riemannZeta (1+movingPoint ρ t N)‖*poleSize N t ≤
      ‖riemannZeta (1+movingPoint ρ t N)‖*(K*‖movingPoint ρ t N‖) := by gcongr
       _ = K*(‖movingPoint ρ t N‖*‖riemannZeta (1+movingPoint ρ t N)‖) := by ring
       _ ≤ K*(M*(1+|t|)^9) := by gcongr
       _ = _ := by ring

private def finiteQ (a t : ℝ) (N : ℕ) : ℂ :=
  ∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+movingPoint a t N))

private theorem finiteQ_nat (a t : ℝ) (N : ℕ) :
    finiteQ a t N=∏ p ∈ Nat.primesLE N,
      (1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I)) := by
  calc finiteQ a t N = ∏ p ∈ Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+movingPoint a t N)) :=
         Finset.prod_coe_sort (Sieve.primeSubtypeLE N)
           (fun p : Nat.Primes => 1-cubicPrimeBase p (1+movingPoint a t N))
       _ = ∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-(1+movingPoint a t N))) :=
         Finset.prod_subtype_of_mem (s := Nat.primesLE N)
           (fun p : ℕ => 1-(p : ℂ)^(-(1+movingPoint a t N)))
           (fun n hn => Nat.prime_of_mem_primesLE hn)
       _ = _ := by
         apply Finset.prod_congr rfl
         intro p hp
         congr 2
         dsimp [movingPoint]
         ring

private theorem uniform_euler_control (A : ℝ) : ∃ E : ℝ, 0<E ∧
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, |a| ≤ |A| → ∀ t : ℝ,
      poleSize N t ≤ E*(1+|t|)^9*‖finiteQ a t N‖ ∧
      ‖finiteQ a t N‖ ≤ E*(1+|t|)^9*poleSize N t := by
  obtain ⟨C,hC,hN⟩ := criticalFiniteEulerProduct_pole_comparison A
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hN,eventually_ge_atTop 2] with N hN hN2
  intro a ha t
  have h := hN a ha t
  rw [← finiteQ_nat] at h
  change ‖movingPoint 1 t N‖ ≤ C*(1+|t|)^9*‖finiteQ a t N‖ ∧
    ‖finiteQ a t N‖ ≤ C*(1+|t|)^9*‖movingPoint 1 t N‖ at h
  have hpole := pole_norm_comparison hN2 t
  constructor
  · calc poleSize N t ≤ 2*‖movingPoint 1 t N‖ := hpole.2
         _ ≤ 2*(C*(1+|t|)^9*‖finiteQ a t N‖) := by gcongr; exact h.1
         _ = _ := by ring
  · calc ‖finiteQ a t N‖ ≤ C*(1+|t|)^9*‖movingPoint 1 t N‖ := h.2
         _ ≤ C*(1+|t|)^9*poleSize N t := by gcongr; exact hpole.1
         _ ≤ (2*C)*(1+|t|)^9*poleSize N t := by
           exact mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_right (show C ≤ 2*C by linarith) (by positivity))
             (poleSize_pos hN2 t).le

private theorem point_sub (a b t u : ℝ) (N : ℕ) :
    movingPoint a t N-movingPoint b u N=movingPoint (a-b) (t-u) N := by
  dsimp [movingPoint]
  push_cast
  ring

private theorem point_neg (a t : ℝ) (N : ℕ) :
    -movingPoint a t N=movingPoint (-a) (-t) N := by
  dsimp [movingPoint]
  push_cast
  ring

private theorem inverse_pole_identity {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    1/(poleSize N t)^2=(Real.log N)^2/(1+Real.log N*|t|)^2 := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have ht : 0<1+Real.log N*|t| := by positivity
  dsimp [poleSize]
  field_simp

private theorem envelope_algebra {Z z₁ z₂ q₁ q₂ q₃ q₄ d₁ d₂ d C B₁ B₂ E T : ℝ}
    (_hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0<q₃) (hq₄ : 0<q₄) (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hd : 0 ≤ d)
    (hC : 0<C) (hB₁ : 0<B₁) (hB₂ : 0<B₂) (hE : 0<E) (hT : 0<T)
    (hs : Z ≤ C*z₁*z₂*(q₁*q₂/(q₃*q₄)))
    (hζ₁ : z₁*d₁ ≤ B₁*T^9) (hζ₂ : z₂*d₂ ≤ B₂*T^9)
    (h₁ : q₁ ≤ E*T^9*d) (h₂ : q₂ ≤ E*T^9*d)
    (h₃ : d₁ ≤ E*T^9*q₃) (h₄ : d₂ ≤ E*T^9*q₄) (hΔ : d ≤ d₁+d₂) :
    Z ≤ (2*C*B₁*B₂*E^4)*T^54*(1/d₁^2+1/d₂^2) := by
  have hzi₁ : z₁ ≤ B₁*T^9/d₁ := (le_div_iff₀ hd₁).mpr hζ₁
  have hzi₂ : z₂ ≤ B₂*T^9/d₂ := (le_div_iff₀ hd₂).mpr hζ₂
  have hi₃ : q₃⁻¹ ≤ E*T^9/d₁ := by
    apply (le_div_iff₀ hd₁).mpr
    calc q₃⁻¹*d₁=d₁/q₃ := by ring
         _ ≤ E*T^9 := (div_le_iff₀ hq₃).mpr h₃
  have hi₄ : q₄⁻¹ ≤ E*T^9/d₂ := by
    apply (le_div_iff₀ hd₂).mpr
    calc q₄⁻¹*d₂=d₂/q₄ := by ring
         _ ≤ E*T^9 := (div_le_iff₀ hq₄).mpr h₄
  have hdsq : d^2 ≤ 2*(d₁^2+d₂^2) := by
    nlinarith [mul_nonneg (show 0 ≤ d₁+d₂-d by linarith)
      (show 0 ≤ d₁+d₂+d by linarith),sq_nonneg (d₁-d₂)]
  calc Z ≤ C*z₁*z₂*(q₁*q₂*(q₃⁻¹*q₄⁻¹)) := by simpa only [div_eq_mul_inv,mul_inv] using hs
       _ ≤ C*(B₁*T^9/d₁)*(B₂*T^9/d₂)*
           ((E*T^9*d)*(E*T^9*d)*((E*T^9/d₁)*(E*T^9/d₂))) := by gcongr
       _ = (C*B₁*B₂*E^4)*T^54*d^2/(d₁^2*d₂^2) := by field_simp
       _ ≤ (C*B₁*B₂*E^4)*T^54*(2*(d₁^2+d₂^2))/(d₁^2*d₂^2) := by gcongr
       _ = _ := by field_simp; ring

private theorem uniform_factor_control (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
      C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
        (‖finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N‖*
          ‖finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N‖/
          (‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖)) := by
  obtain ⟨C,hC,hN⟩ := criticalCompletedConeEuler_uniform_factor_bound ρ₁ ρ₂
  refine ⟨C,hC,?_⟩
  filter_upwards [hN] with N hN
  intro t₁ t₂
  have h := hN t₁ t₂
  change ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
    C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
      ‖((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p
            (1+(movingPoint ρ₂ t₂ N-movingPoint ρ₁ t₁ N))))*
        (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p
            (1+(movingPoint ρ₁ t₁ N-movingPoint ρ₂ t₂ N)))))/
        ((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-movingPoint ρ₁ t₁ N)))*
          (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-movingPoint ρ₂ t₂ N))))‖ at h
  have hneg (a t : ℝ) : 1-movingPoint a t N=1+movingPoint (-a) (-t) N := by
    rw [sub_eq_add_neg,point_neg]
  simp only [point_sub,hneg] at h
  change ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
    C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
      ‖(finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N*
        finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N)/
        (finiteQ (-(ρ₁ : ℝ)) (-t₁) N*finiteQ (-(ρ₂ : ℝ)) (-t₂) N)‖ at h
  simpa only [norm_div,norm_mul] using h

/-- A global axes envelope with an integrable transverse profile and a polynomial
frequency weight for the COMPLETE original source. All real frequency
pairs are controlled simultaneously at the original prime cutoff. -/
theorem criticalCompletedConeEuler_uniform_axes_bound (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+(((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(t₁ : ℂ)*Complex.I)
        (1+(((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(t₂ : ℂ)*Complex.I)‖ ≤
      C*(1+|t₁|+|t₂|)^54 *
        ((Real.log N)^2/(1+Real.log N*|t₁|)^2+
          (Real.log N)^2/(1+Real.log N*|t₂|)^2) := by
  obtain ⟨C₀,hC₀,hsource⟩ := uniform_factor_control ρ₁ ρ₂
  obtain ⟨B₁,hB₁,hz₁⟩ := zeta_pole_bound ρ₁
  obtain ⟨B₂,hB₂,hz₂⟩ := zeta_pole_bound ρ₂
  let A : ℝ := |(ρ₁ : ℝ)|+|(ρ₂ : ℝ)|
  obtain ⟨E,hE,heuler⟩ := uniform_euler_control A
  refine ⟨2*C₀*B₁*B₂*E^4,by positivity,?_⟩
  filter_upwards [hsource,hz₁,hz₂,heuler,eventually_ge_atTop 2] with N hs hz₁ hz₂ he hN
  intro t₁ t₂
  let T : ℝ := 1+|t₁|+|t₂|
  have hT : 0<T := by dsimp [T]; positivity
  have hT₁ : 1+|t₁| ≤ T := by dsimp [T]; linarith [abs_nonneg t₂]
  have hT₂ : 1+|t₂| ≤ T := by dsimp [T]; linarith [abs_nonneg t₁]
  have hTΔ : 1+|t₂-t₁| ≤ T := by dsimp [T]; linarith [abs_sub t₂ t₁]
  have hTΔ' : 1+|t₁-t₂| ≤ T := by dsimp [T]; linarith [abs_sub t₁ t₂]
  have hA₁ : |-(ρ₁ : ℝ)| ≤ |A| := by
    rw [abs_neg]
    exact (le_add_of_nonneg_right (abs_nonneg (ρ₂ : ℝ))).trans (le_abs_self A)
  have hA₂ : |-(ρ₂ : ℝ)| ≤ |A| := by
    rw [abs_neg]
    exact (le_add_of_nonneg_left (abs_nonneg (ρ₁ : ℝ))).trans (le_abs_self A)
  have hAΔ : |(ρ₂ : ℝ)-(ρ₁ : ℝ)| ≤ |A| := by
    have hh : |(ρ₂ : ℝ)-(ρ₁ : ℝ)| ≤ A := by dsimp [A]; linarith [abs_sub (ρ₂ : ℝ) (ρ₁ : ℝ)]
    exact hh.trans (le_abs_self A)
  have hAΔ' : |(ρ₁ : ℝ)-(ρ₂ : ℝ)| ≤ |A| := by
    have hh : |(ρ₁ : ℝ)-(ρ₂ : ℝ)| ≤ A := by dsimp [A]; exact abs_sub _ _
    exact hh.trans (le_abs_self A)
  have hqe₁ := he ((ρ₂ : ℝ)-(ρ₁ : ℝ)) hAΔ (t₂-t₁)
  have hqe₂ := he ((ρ₁ : ℝ)-(ρ₂ : ℝ)) hAΔ' (t₁-t₂)
  have hqe₃ := he (-(ρ₁ : ℝ)) hA₁ (-t₁)
  have hqe₄ := he (-(ρ₂ : ℝ)) hA₂ (-t₂)
  have hdp : 0 ≤ poleSize N (t₂-t₁) := (poleSize_pos hN (t₂-t₁)).le
  have hq₁ : ‖finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N‖ ≤ E*T^9*poleSize N (t₂-t₁) := by
    apply hqe₁.2.trans
    gcongr
  have hq₂ : ‖finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N‖ ≤ E*T^9*poleSize N (t₂-t₁) := by
    have hp : poleSize N (t₁-t₂)=poleSize N (t₂-t₁) := by simp only [poleSize,abs_sub_comm t₁ t₂]
    have hh := hqe₂.2
    rw [hp] at hh
    apply hh.trans
    gcongr
  have hq₃ : poleSize N t₁ ≤ E*T^9*‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
    have hh : poleSize N t₁ ≤ E*(1+|t₁|)^9*‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
      simpa only [poleSize,abs_neg] using hqe₃.1
    apply hh.trans
    gcongr
  have hq₄ : poleSize N t₂ ≤ E*T^9*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
    have hh : poleSize N t₂ ≤ E*(1+|t₂|)^9*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
      simpa only [poleSize,abs_neg] using hqe₄.1
    apply hh.trans
    gcongr
  have hQ₃ : 0<‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
    by_contra hh
    have hzero : ‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hzero,mul_zero] at hq₃
    exact (not_le_of_gt (poleSize_pos hN t₁)) hq₃
  have hQ₄ : 0<‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
    by_contra hh
    have hzero : ‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hzero,mul_zero] at hq₄
    exact (not_le_of_gt (poleSize_pos hN t₂)) hq₄
  have hζ₁ : ‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*poleSize N t₁ ≤ B₁*T^9 := by
    apply (hz₁ t₁).trans
    gcongr
  have hζ₂ : ‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*poleSize N t₂ ≤ B₂*T^9 := by
    apply (hz₂ t₂).trans
    gcongr
  have hΔ : poleSize N (t₂-t₁) ≤ poleSize N t₁+poleSize N t₂ := by
    have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
    have heps : 0<1/Real.log N := by positivity
    dsimp [poleSize]
    linarith [abs_sub t₂ t₁]
  have hh := envelope_algebra
    (norm_nonneg (riemannZeta (1+movingPoint ρ₁ t₁ N)))
    (norm_nonneg (riemannZeta (1+movingPoint ρ₂ t₂ N)))
    (norm_nonneg (finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N))
    (norm_nonneg (finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N))
    hQ₃ hQ₄ (poleSize_pos hN t₁) (poleSize_pos hN t₂) (poleSize_pos hN (t₂-t₁)).le
    hC₀ hB₁ hB₂ hE hT (hs t₁ t₂) hζ₁ hζ₂ hq₁ hq₂ hq₃ hq₄ hΔ
  rw [inverse_pole_identity hN t₁,inverse_pole_identity hN t₂] at hh
  simpa only [T,movingPoint,add_assoc] using hh

end RHTower.BAGTrace
