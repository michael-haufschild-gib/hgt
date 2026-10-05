import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPoisson
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicCriticalAtoms

/-!
# Complete lifted critical physical cubic action

The full shifted Fourier lattice equals the literal unmasked smooth physical
cube test. Applying the existing critical rational tensor and both literal
contraction projectors therefore recovers the entire smoothed signed cubic.
An unconditional family preserves every Fourier lift and the negligible
comparison with the original sharp cubic. No signed saving is assumed or proved.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff
namespace RHTower.BAGTrace

private def realTriple (x : ℝ × ℝ × ℝ) : BAGPhysicalSpace :=
  WithLp.toLp 2 ![x.1,x.2.1,x.2.2]

def bagLiftedFourierTest (A : SchwartzMap BAGPhysicalSpace ℂ) (x : ℝ × ℝ × ℝ) : ℂ :=
  ∑' k : ℤ × ℤ × ℤ, (𝓕 A) (bagIntegerTriple k-realTriple x)

private lemma phase (n : ℤ × ℤ × ℤ) (x : ℝ × ℝ × ℝ) :
    Complex.exp ((2*Real.pi*inner ℝ (bagIntegerTriple n) (realTriple x) : ℝ)*Complex.I) =
      ramanujanTripleFourierPhase n x := by
  simp only [bagIntegerTriple,realTriple,PiLp.inner_apply,Real.inner_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,
    ramanujanTripleFourierPhase,ramanujanFourierPhase]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

private def natTriple (n : ℕ × ℕ × ℕ) : ℤ × ℤ × ℤ := (n.2.1,n.2.2,n.1)
private lemma natTriple_injective : Function.Injective natTriple := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) h
  have h3 := congrArg (fun x : ℤ × ℤ × ℤ => x.2.2) h
  dsimp only [natTriple] at h1 h2 h3
  have he1 : a.1=b.1 := by exact_mod_cast h3
  have he2 : a.2.1=b.2.1 := by exact_mod_cast h1
  have he3 : a.2.2=b.2.2 := by exact_mod_cast h2
  exact Prod.ext he1 (Prod.ext he2 he3)

private lemma nat_band {N : ℝ} (hN : 0 ≤ N) {z : ℤ} (hz : (z : ℝ) ∈ Ioo N (2*N)) :
    ∃ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, (n : ℤ)=z := by
  have hz0 : 0 ≤ z := by exact_mod_cast (hN.trans hz.1.le)
  have he : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz0
  have heR : (z.toNat : ℝ)=(z : ℝ) := by exact_mod_cast he
  refine ⟨z.toNat,?_,he⟩
  rw [Finset.mem_Ioc]
  constructor
  · exact (Nat.floor_lt hN).mpr (heR ▸ hz.1)
  · exact (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2*N)).mpr (heR ▸ hz.2.le)

private lemma amplitude_support {N : ℝ} (hN : 0 ≤ N) {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (k : ℤ × ℤ × ℤ)
    (hk : bagCubicPhysicalAmplitude N η (bagIntegerTriple k) ≠ 0) :
    k ∈ ((Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) ×ˢ
      ((Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊) ×ˢ (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊))).image natTriple := by
  classical
  have hc (i : Fin 3) : bagIntegerTriple k i ∈ Ioo N (2*N) := by
    by_contra hi
    have he := hz _ hi
    apply hk
    fin_cases i <;> simp_all [bagCubicPhysicalAmplitude,bagCubicMellinSliceValue]
  obtain ⟨p,hp,hep⟩ := nat_band hN (by simpa [bagIntegerTriple] using hc 0)
  obtain ⟨q,hq,heq⟩ := nat_band hN (by simpa [bagIntegerTriple] using hc 1)
  obtain ⟨r,hr,her⟩ := nat_band hN (by simpa [bagIntegerTriple] using hc 2)
  exact Finset.mem_image.mpr ⟨(r,p,q),by simp only [Finset.mem_product]; exact ⟨hr,hp,hq⟩,
    by simp only [natTriple,hep,heq,her]⟩

/-- Every Fourier lift equals the actual unmasked finite physical test. -/
theorem bagLiftedFourierTest_eq_finite {N : ℝ} (hN : 0 ≤ N) {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ)
    (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    bagLiftedFourierTest A = ramanujanFiniteCubeTest (Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊)
      (fun p q r => bagCubicPhysicalAmplitude N η (bagIntegerTriple (p,q,r))) := by
  classical
  have hc : HasCompactSupport (A : BAGPhysicalSpace → ℂ) := by
    rw [show (A : BAGPhysicalSpace → ℂ)=bagCubicPhysicalAmplitude N η from funext hA]
    exact hasCompactSupport_bagCubicPhysicalAmplitude N hz
  ext x
  unfold bagLiftedFourierTest
  rw [FullPoisson.full_poisson A hc]
  let S := Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊
  rw [tsum_eq_sum (s := (S ×ˢ (S ×ˢ S)).image natTriple) (fun k hk => ?_)]
  · rw [Finset.sum_image natTriple_injective.injOn,Finset.sum_product]
    simp only [Finset.sum_product,ramanujanFiniteCubeTest,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [phase,hA]
    dsimp only [natTriple]
    rw [mul_comm]
  · have he : bagCubicPhysicalAmplitude N η (bagIntegerTriple k)=0 := by
      by_contra hn
      exact hk (amplitude_support hN hz k hn)
    rw [hA,he,mul_zero]

/-- Complete lifted critical action, with both literal contraction projectors. -/
theorem primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction {N : ℝ} (hN : 1 ≤ N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ)
    (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    primeGaussianCubicSmoothedOffDiagonal N η =
      ramanujanCriticalTripleAtomAction (Finset.range (⌊2*N⌋₊+1))
        (ramanujanNoncontractingProjector (⌊2*N⌋₊+1) (bagLiftedFourierTest A)) := by
  classical
  have hf : 1 ≤ ⌊N⌋₊ := by simpa using Nat.floor_mono hN
  have hS : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, 1 < n ∧ n ≤ ⌊2*N⌋₊ := by
    intro n hn
    exact ⟨lt_of_le_of_lt hf (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2⟩
  rw [bagLiftedFourierTest_eq_finite (zero_le_one.trans hN) hz A hA,
    ramanujanCriticalTripleAtomAction_projected_cube _ _ hS]
  have hreorder : primeGaussianCubicSmoothedOffDiagonal N η =
      ∑ r ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
        (η p : ℂ)*(η q : ℂ)*(η r : ℂ)*
          (if p=r ∨ q=r then 0 else primeGaussianCubicMainEntry N p q r) := by
    unfold primeGaussianCubicSmoothedOffDiagonal
    calc
      _ = ∑ p ∈ primeProfileBand N, ∑ r ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
          (η p : ℂ)*(η q : ℂ)*(η r : ℂ)*
            (if p=r ∨ q=r then 0 else primeGaussianCubicMainEntry N p q r) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hreorder]
  unfold primeProfileBand
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrp : r.Prime
  · simp only [if_pos hrp]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime
    · simp only [if_pos hpp]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqp : q.Prime
      · simp only [if_pos hqp]
        by_cases hm : p=r ∨ q=r
        · simp [hm]
        · have hl (n : ℕ) (hn : n.Prime) : (Real.log n : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
          rw [if_neg hm,if_neg hm,bagCubicPhysicalAmplitude_nat]
          simp only [Complex.ofReal_mul]
          exact (div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero (hl p hpp) (hl q hqp))
            (hl r hrp))).symm
      · simp [hqp]
    · simp [hpp]
  · simp [hrp]

/-- An unconditional family identifies the entire signed physical cubic,
up to its audited negligible edge error, with the full lifted atom action. -/
theorem exists_bagCompleteLiftedCriticalAction :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖(𝓕 (A N)) (bagIntegerTriple k-a)‖)) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N) =
          ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1) (bagLiftedFourierTest (A N)))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
            (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1)
              (bagLiftedFourierTest (A N)))‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalPoissonFamily
  have he : ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N (η N) =
        ramanujanCriticalTripleAtomAction (Finset.range (⌊2*(N : ℝ)⌋₊+1))
          (ramanujanNoncontractingProjector (⌊2*(N : ℝ)⌋₊+1) (bagLiftedFourierTest (A N))) := by
    filter_upwards [hA,eventually_ge_atTop (1 : ℕ)] with N hreg hN
    exact primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction
      (by exact_mod_cast hN) hreg.2.2.2.1 (A N) hreg.2.2.2.2.2.1
  refine ⟨η,A,?_,?_⟩
  · filter_upwards [hA,he] with N hreg heq
    exact ⟨hreg.2.2.2.2.2.1,hreg.2.2.2.2.2.2.2.1,heq⟩
  · apply herr.congr'
    filter_upwards [he] with N heq
    rw [heq]

end RHTower.BAGTrace
