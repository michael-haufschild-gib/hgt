import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicWindowTransition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries

/-!
# Full physical cubic Fourier lattice summability

The literal three-coordinate Gaussian/logarithmic amplitude is smooth and
compactly supported, including its reciprocal r-factor and moving physical
window. Its Fourier transform is absolutely summable on every shifted full
integer triple lattice. An unconditional family retains the existing
negligible sharp/smooth comparison. No Poisson identity or signed cubic
saving is asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform ContDiff Topology
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

abbrev BAGPhysicalSpace := EuclideanSpace ℝ (Fin 3)

def bagIntegerTriple (k : ℤ × ℤ × ℤ) : BAGPhysicalSpace :=
  WithLp.toLp 2 ![(k.1 : ℝ), (k.2.1 : ℝ), (k.2.2 : ℝ)]

private def latticeWeight (n : ℤ) : ℝ := (1 + (n : ℝ)^2)⁻¹

private theorem latticeWeight_nonneg (n : ℤ) : 0 ≤ latticeWeight n := by
  unfold latticeWeight
  positivity

private theorem latticeWeight_summable : Summable latticeWeight := by
  have h : Summable (fun n : ℤ => 1 / (n : ℝ)^2 + if n=0 then 1 else 0) :=
    (Real.summable_one_div_int_pow.mpr one_lt_two).add
      (summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp_all))
  apply Summable.of_nonneg_of_le latticeWeight_nonneg _ h
  intro n
  by_cases hn : n=0
  · subst n; simp [latticeWeight]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [if_neg hn,add_zero,one_div,latticeWeight]
    exact inv_anti₀ (sq_pos_of_ne_zero hn') (by linarith [sq_nonneg (n : ℝ)])

/-- Absolute sampling of the entire integer triple lattice, with no omitted lifts. -/
theorem summable_norm_bagIntegerTriple (f : SchwartzMap BAGPhysicalSpace ℂ) :
    Summable (fun k : ℤ × ℤ × ℤ => ‖f (bagIntegerTriple k)‖) := by
  let C : ℝ := 2^6 * (Finset.Iic (6,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
  have hd (x : BAGPhysicalSpace) : (1+‖x‖)^6*‖f x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (6,0)) (k := 6) (n := 0) le_rfl le_rfl f x)
  have hs := latticeWeight_summable.mul_of_nonneg
    (latticeWeight_summable.mul_of_nonneg latticeWeight_summable
      latticeWeight_nonneg latticeWeight_nonneg)
    latticeWeight_nonneg (fun _ => mul_nonneg (latticeWeight_nonneg _) (latticeWeight_nonneg _))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left C)
  intro k
  let x := bagIntegerTriple k
  have hp (i : Fin 3) : 1+(x i)^2 ≤ (1+‖x‖)^2 := by
    have h := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at h
    have hs : (x i)^2 ≤ ‖x‖^2 := by
      nlinarith only [sq_abs (x i),mul_nonneg (sub_nonneg.mpr h)
        (add_nonneg (norm_nonneg x) (abs_nonneg (x i)))]
    nlinarith [norm_nonneg x]
  have hden : (1+(k.1 : ℝ)^2)*((1+(k.2.1 : ℝ)^2)*(1+(k.2.2 : ℝ)^2)) ≤ (1+‖x‖)^6 := by
    calc
      _ ≤ ((1+‖x‖)^2)*(((1+‖x‖)^2)*((1+‖x‖)^2)) := by
        apply mul_le_mul
        · simpa [x,bagIntegerTriple] using hp 0
        · apply mul_le_mul
          · simpa [x,bagIntegerTriple] using hp 1
          · simpa [x,bagIntegerTriple] using hp 2
          · positivity
          · positivity
        · positivity
        · positivity
      _ = _ := by ring
  have hpos : 0 < (1+(k.1 : ℝ)^2)*((1+(k.2.1 : ℝ)^2)*(1+(k.2.2 : ℝ)^2)) := by positivity
  have hb := (mul_le_mul_of_nonneg_right hden (norm_nonneg (f x))).trans (hd x)
  have hh : ‖f x‖ ≤ C / ((1+(k.1 : ℝ)^2)*((1+(k.2.1 : ℝ)^2)*(1+(k.2.2 : ℝ)^2))) := by
    apply (le_div_iff₀ hpos).mpr
    simpa only [mul_comm] using hb
  simpa only [div_eq_mul_inv,mul_inv_rev,latticeWeight,mul_comm,mul_left_comm,mul_assoc] using hh

/-- Every real translate retains absolute convergence on the full integer lattice. -/
theorem summable_norm_bagIntegerTriple_add (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a : BAGPhysicalSpace) :
    Summable (fun k : ℤ × ℤ × ℤ => ‖f (bagIntegerTriple k+a)‖) := by
  simpa only [SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add] using
    summable_norm_bagIntegerTriple (f.compSubConstCLM ℂ (-a))

/-- Full Fourier lattice summability, for every three-frequency shift. -/
theorem summable_norm_bagFourierIntegerTriple (f : SchwartzMap BAGPhysicalSpace ℂ)
    (a : BAGPhysicalSpace) :
    Summable (fun k : ℤ × ℤ × ℤ => ‖(𝓕 f) (bagIntegerTriple k+a)‖) :=
  summable_norm_bagIntegerTriple_add (𝓕 f) a



/-- The entire physical cubic amplitude, including its third coordinate. -/
def bagCubicPhysicalAmplitude (N : ℝ) (η : ℝ → ℝ) (v : BAGPhysicalSpace) : ℂ :=
  (2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 (v 0)*
    bagCubicMellinSliceValue N η 0 (v 1)*
    (starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 (v 2)) / (v 2 : ℂ)*
    (bagPhysicalHeightWindow (v 0*v 1/(v 2*N)) : ℂ)*
    bourgainOscillation (2*Real.pi*(v 0*v 1/v 2))

private theorem amplitude_zero_of_slice_zero (N : ℝ) (η : ℝ → ℝ)
    (v : BAGPhysicalSpace) (i : Fin 3)
    (h : bagCubicMellinSliceValue N η 0 (v i)=0) :
    bagCubicPhysicalAmplitude N η v=0 := by
  fin_cases i <;> simp_all [bagCubicPhysicalAmplitude]

/-- All derivatives exist across the excluded reciprocal singularity. -/
theorem contDiff_bagCubicPhysicalAmplitude {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) :
    ContDiff ℝ ∞ (bagCubicPhysicalAmplitude N η) := by
  have heval (i : Fin 3) : ContDiff ℝ ∞ (fun v : BAGPhysicalSpace => v i) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : BAGPhysicalSpace →L[ℝ] ℝ).contDiff
  have hF (i : Fin 3) : ContDiff ℝ ∞ (fun v : BAGPhysicalSpace => bagCubicMellinSliceValue N η 0 (v i)) :=
    (contDiff_bagCubicMellinSliceValue hN hη hz 0).comp (heval i)
  have hFc := Complex.conjCLE.contDiff.comp (hF 2)
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hr : 1 < v 2
  · have hr0 : v 2 ≠ 0 := ne_of_gt (by linarith)
    have hR : ContDiffAt ℝ ∞ (fun w : BAGPhysicalSpace => w 0*w 1/w 2) v :=
      ((heval 0).contDiffAt.mul (heval 1).contDiffAt).div (heval 2).contDiffAt hr0
    have hW : ContDiffAt ℝ ∞ (fun w : BAGPhysicalSpace =>
        (bagPhysicalHeightWindow (w 0*w 1/(w 2*N)) : ℂ)) v := by
      have hw := (Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff).contDiffAt.comp v
        (hR.div_const N)
      simpa only [div_div,Function.comp_def,Complex.ofRealCLM_apply] using hw
    have hphase : ContDiffAt ℝ ∞ (fun w : BAGPhysicalSpace =>
        bourgainOscillation (2*Real.pi*(w 0*w 1/w 2))) v := by
      unfold bourgainOscillation
      exact Complex.contDiff_exp.contDiffAt.comp v
        (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (contDiffAt_const.mul hR)))
    have hi : ContDiffAt ℝ ∞ (fun w : BAGPhysicalSpace => (w 2 : ℂ)⁻¹) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v (heval 2).contDiffAt).inv
        (Complex.ofReal_ne_zero.mpr hr0)
    change ContDiffAt ℝ ∞ (fun w : BAGPhysicalSpace =>
      (2*Real.pi : ℂ)*bagCubicMellinSliceValue N η 0 (w 0)*
        bagCubicMellinSliceValue N η 0 (w 1)*
        (starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 (w 2)) / (w 2 : ℂ)*
        (bagPhysicalHeightWindow (w 0*w 1/(w 2*N)) : ℂ)*
        bourgainOscillation (2*Real.pi*(w 0*w 1/w 2))) v
    simpa only [div_eq_mul_inv,Pi.inv_apply,Function.comp_apply,Complex.conjCLE_apply] using
      (((((contDiffAt_const.mul (hF 0).contDiffAt).mul (hF 1).contDiffAt).mul
        hFc.contDiffAt).mul hi).mul hW).mul hphase
  · have heq : bagCubicPhysicalAmplitude N η =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      have hn : (fun w : BAGPhysicalSpace => w 2) ⁻¹' Iio N ∈ 𝓝 v :=
        (heval 2).continuous.continuousAt.preimage_mem_nhds
          (Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt hr) hN))
      filter_upwards [hn] with w hw
      apply amplitude_zero_of_slice_zero N η w 2
      have hzero : η (w 2)=0 := hz _ (fun h => (not_lt_of_ge hw.le) h.1)
      simp [bagCubicMellinSliceValue,hzero]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq

/-- Compactness uses all three actual cutoff coordinates, including r. -/
theorem hasCompactSupport_bagCubicPhysicalAmplitude (N : ℝ) {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) :
    HasCompactSupport (bagCubicPhysicalAmplitude N η) := by
  classical
  let K : Set BAGPhysicalSpace := {v | ∀ i, v i ∈ Icc N (2*N)}
  have hK : IsCompact K := by
    have he : K = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
        (Set.univ.pi (fun _ : Fin 3 => Icc N (2*N))) := by
      ext v
      change (∀ i, v i ∈ Icc N (2*N)) ↔ ∀ i ∈ (Set.univ : Set (Fin 3)), v i ∈ Icc N (2*N)
      simp
    rw [he]
    exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := N) (b := 2*N)))
  apply HasCompactSupport.intro' hK hK.isClosed
  intro v hv
  change ¬ ∀ i, v i ∈ Icc N (2*N) at hv
  push Not at hv
  obtain ⟨i,hi⟩ := hv
  apply amplitude_zero_of_slice_zero N η v i
  have hzero : η (v i)=0 := hz _ (fun h => hi ⟨h.1.le,h.2.le⟩)
  simp [bagCubicMellinSliceValue,hzero]

/-- The actual full three-coordinate physical amplitude as a Schwartz function. -/
def bagCubicPhysicalSchwartz {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) :
    SchwartzMap BAGPhysicalSpace ℂ :=
  (hasCompactSupport_bagCubicPhysicalAmplitude N hz).toSchwartzMap
    (contDiff_bagCubicPhysicalAmplitude hN hη hz)

/-- Every full lifted Fourier family of the actual physical amplitude is absolutely
summable. All three coordinates and all integer lifts are retained. -/
theorem summable_norm_bagCubicPhysicalFourier {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (a : BAGPhysicalSpace) :
    Summable (fun k : ℤ × ℤ × ℤ =>
      ‖(𝓕 (bagCubicPhysicalSchwartz hN hη hz)) (bagIntegerTriple k+a)‖) :=
  summable_norm_bagFourierIntegerTriple _ _

/-- The continuous amplitude has exactly the original cubic main coefficients
at integer triples, with the three cutoff and logarithmic factors explicit. -/
theorem bagCubicPhysicalAmplitude_nat (N : ℝ) (η : ℝ → ℝ) (p q r : ℕ) :
    bagCubicPhysicalAmplitude N η (bagIntegerTriple (p,q,r)) =
      ((η p*η q*η r : ℝ) : ℂ)*primeGaussianCubicMainEntry N p q r /
        ((Real.log p : ℂ)*(Real.log q : ℂ)*(Real.log r : ℂ)) := by
  have h0 : bagIntegerTriple (p,q,r) 0=(p : ℝ) := by simp [bagIntegerTriple]
  have h1 : bagIntegerTriple (p,q,r) 1=(q : ℝ) := by simp [bagIntegerTriple]
  have h2 : bagIntegerTriple (p,q,r) 2=(r : ℝ) := by simp [bagIntegerTriple]
  have hb : bourgainOscillation 0=1 := by simp [bourgainOscillation]
  rw [bagCubicPhysicalAmplitude,h0,h1,h2]
  simp only [bagCubicMellinSliceValue,primeGaussianCubicMainEntry,neg_zero,zero_mul,
    hb,mul_one,map_mul,map_div₀,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Unconditional actual family with every three-coordinate Fourier lift,
absolute summability at every shift and the established negligible edge error. -/
theorem exists_bagCubicPhysicalFourierFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖(𝓕 (A N)) (bagIntegerTriple k+a)‖))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          primeGaussianCubicSmoothedOffDiagonal N (η N)‖) atTop (𝓝 0) := by
  classical
  obtain ⟨η,hη,herr⟩ := exists_primeGaussianCubic_smooth_band_negligible_error
  let Good : ℕ → Prop := fun N => 1 < (N : ℝ) ∧
    ContDiff ℝ ∞ (η N) ∧ (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0)
  have hg : ∀ᶠ N : ℕ in atTop, Good N := by
    filter_upwards [hη,eventually_ge_atTop (2 : ℕ)] with N hreg hN
    exact ⟨by exact_mod_cast (by omega : 1 < N),hreg.1,hreg.2.2.2.1⟩
  let A : ℕ → SchwartzMap BAGPhysicalSpace ℂ := fun N =>
    if h : Good N then bagCubicPhysicalSchwartz h.1 h.2.1 h.2.2 else 0
  refine ⟨η,A,?_,herr⟩
  filter_upwards [hη,hg] with N hreg hgood
  obtain ⟨hsm,hco,hbo,hze,hpl⟩ := hreg
  refine ⟨hsm,hco,hbo,hze,hpl,?_,?_⟩
  · intro v
    dsimp [A]
    rw [dif_pos hgood]
    rfl
  · exact fun a => summable_norm_bagFourierIntegerTriple (A N) a

end RHTower.BAGTrace
