import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Observable eigenvectors and collisions of a Cauchy response matrix

The inverse Jordan image of a rank-one real source satisfies a rank-one
displacement identity. On an eigenvector it equates the squared source
reading to its eigenvalue times a positive rate-weighted norm. All nonzero
eigenspaces are therefore one-dimensional. The zero eigenspace consists
exactly of the cancellations inside sets of equal rates.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.CauchySpectrum
open Matrix Finset CauchyJordan
variable {n : ℕ}

/-- Real matrix of the inverse Jordan response to the source b bᵀ. -/
def response (r b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 2*b i*b j/(rate r i+rate r j)

theorem response_jordan (r b : Fin n → ℝ) :
    (response r b).map Complex.ofReal =
      inverseJordan r (fun i j => ((b i:ℂ)*(b j:ℂ))) := by
  ext i j
  simp only [Matrix.map_apply,response,inverseJordan,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_ofNat]
  ring

def reading (b v : Fin n → ℝ) := ∑ i, b i*v i

def energy (r v : Fin n → ℝ) := ∑ i, rate r i*v i^2

/-- The displacement has rank at most one, with its scale fixed by the Jordan convention. -/
theorem displacement (r b : Fin n → ℝ) (i j : Fin n) :
    (rate r i+rate r j)*response r b i j = 2*b i*b j := by
  unfold response
  field_simp [(add_pos (rate_pos r i) (rate_pos r j)).ne']

private theorem symmetric (r b : Fin n → ℝ) (i j : Fin n) :
    response r b i j = response r b j i := by unfold response; rw [add_comm]; ring

/-- Multiplying an input by the rate minus a constant can be transferred to
the output, with only a scalar source reading left over. -/
theorem shifted_action (r b v : Fin n → ℝ) (s : ℝ) (i : Fin n) :
    ((response r b).mulVec (fun j => (rate r j-s)*v j)) i =
      2*b i*reading b v-(rate r i+s)*((response r b).mulVec v) i := by
  simp only [Matrix.mulVec,dotProduct,reading,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination v j*displacement r b i j

private theorem transpose_sum (r b u v : Fin n → ℝ) :
    (∑ i, u i*((response r b).mulVec v) i) = ∑ j, ((response r b).mulVec u) j*v j := by
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symmetric r b j i]
  ring

/-- Polarized displacement identity on two different inputs. -/
theorem polarized_reading (r b u v : Fin n → ℝ) :
    2*reading b u*reading b v =
      (∑ i, rate r i*u i*((response r b).mulVec v) i) +
      (∑ i, rate r i*v i*((response r b).mulVec u) i) := by
  have h := transpose_sum r b u (fun i => rate r i*v i)
  have hrow (i : Fin n) : ((response r b).mulVec (fun j => rate r j*v j)) i =
      2*b i*reading b v-rate r i*((response r b).mulVec v) i := by
    simpa only [sub_zero,add_zero] using shifted_action r b v 0 i
  simp_rw [hrow] at h
  have hL : (∑ i, u i*(2*b i*reading b v-rate r i*((response r b).mulVec v) i)) =
      2*reading b u*reading b v - ∑ i, rate r i*u i*((response r b).mulVec v) i := by
    have he : 2*reading b u*reading b v = ∑ i, (b i*u i)*(2*reading b v) := by
      rw [← Finset.sum_mul]
      change 2*reading b u*reading b v = reading b u*(2*reading b v)
      ring
    rw [he,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hL] at h
  have hR : (∑ i, ((response r b).mulVec u) i*(rate r i*v i)) =
      ∑ i, rate r i*v i*((response r b).mulVec u) i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith only [h,hR]

/-- Every eigenvalue equals a squared source reading divided by positive energy. -/
theorem eigen_reading (r b v : Fin n → ℝ) (level : ℝ) :
    (response r b).mulVec v = level • v → reading b v^2 = level*energy r v := by
  intro he
  have h := polarized_reading r b v v
  rw [he] at h
  have hs : (∑ i, rate r i*v i*(level • v) i) = level*energy r v := by
    unfold energy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change _*(_*_) = _
    ring
  rw [hs] at h
  linear_combination h/2

theorem energy_pos_iff (r v : Fin n → ℝ) : 0 < energy r v ↔ v ≠ 0 := by
  constructor
  · rintro h rfl
    simp [energy] at h
  · intro hv
    classical
    have hi : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.sum_pos' (fun j _ => mul_nonneg (rate_pos r j).le (sq_nonneg _))
      ⟨i,mem_univ _,mul_pos (rate_pos _ _) (sq_pos_of_ne_zero hi)⟩

/-- All real eigenvalues on nonzero vectors are nonnegative, and exactly the
zero eigenvalue is invisible to the source reading. -/
theorem eigenvalue_detection (r b : Fin n → ℝ) (v : {v : Fin n → ℝ // v ≠ 0}) (level : ℝ) :
    (response r b).mulVec v.val = level • v.val →
      0 ≤ level ∧ (reading b v.val = 0 ↔ level = 0) := by
  intro he
  have hv := (energy_pos_iff r v.val).mpr v.property
  have h := eigen_reading r b v.val level he
  refine ⟨nonneg_of_mul_nonneg_left (h ▸ sq_nonneg (reading b v.val)) hv,?_⟩
  rw [← sq_eq_zero_iff,h,mul_eq_zero,or_iff_left hv.ne']

/-- Within one nonzero eigenvalue the source reading determines the eigenvector. -/
theorem simple_eigenvectors (r b u v : Fin n → ℝ) (level : ℝ) :
    (response r b).mulVec u = level • u → (response r b).mulVec v = level • v →
      level=0 ∨ reading b v • u = reading b u • v := by
  intro hu hv
  by_cases hλ : level=0
  · exact Or.inl hλ
  right
  let w := reading b v • u - reading b u • v
  have he : (response r b).mulVec w = level • w := by
    simp only [w,Matrix.mulVec_sub,Matrix.mulVec_smul,hu,hv,smul_sub,smul_comm level]
  have hw : reading b w = 0 := by
    have lin (x : ℝ) (y : Fin n → ℝ) : reading b (x • y) = x*reading b y := by
      simp only [reading,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have sub (x y : Fin n → ℝ) : reading b (x-y) = reading b x-reading b y := by
      simp only [reading,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
    change reading b (reading b v • u - reading b u • v) = 0
    rw [sub,lin,lin,mul_comm,sub_self]
  apply sub_eq_zero.mp
  change w = 0
  by_contra hz
  exact hλ ((eigenvalue_detection r b ⟨w,hz⟩ level he).2.mp hw)

/-- Symmetry of the real inverse Jordan response. -/
theorem response_hermitian (r b : Fin n → ℝ) : (response r b).IsHermitian := by
  ext i j
  simpa only [Matrix.conjTranspose_apply,star_trivial] using symmetric r b j i

private abbrev spectralBasis (r b : Fin n → ℝ) := (response_hermitian r b).eigenvectorBasis

/-- All spectral levels are nonnegative, including when source components vanish. -/
theorem levels_nonnegative (r b : Fin n → ℝ) (i : Fin n) :
    0 ≤ (response_hermitian r b).eigenvalues i := by
  have hn := (WithLp.ofLp_eq_zero 2).ne.2 ((spectralBasis r b).orthonormal.ne_zero i)
  exact (eigenvalue_detection r b ⟨_,hn⟩ _ ((response_hermitian r b).mulVec_eigenvectorBasis i)).1

/-- Only zero can repeat in the full eigenvalue list, even for colliding rates. -/
theorem spectral_collision (r b : Fin n → ℝ) (i j : Fin n) :
    (response_hermitian r b).eigenvalues i = (response_hermitian r b).eigenvalues j →
      i=j ∨ (response_hermitian r b).eigenvalues j=0 := by
  intro he
  by_cases hij : i=j
  · exact Or.inl hij
  right
  by_contra hne
  let B := spectralBasis r b
  have hi := (response_hermitian r b).mulVec_eigenvectorBasis i
  have hj := (response_hermitian r b).mulVec_eigenvectorBasis j
  rw [he] at hi
  have h := (simple_eigenvectors r b _ _ _ hi hj).resolve_left hne
  have hb : reading b (B j).ofLp • B i = reading b (B i).ofLp • B j := by
    simpa only [WithLp.toLp_smul,WithLp.toLp_ofLp] using congrArg (WithLp.toLp 2) h
  have hh := congrArg (fun v => inner ℝ (B i) v) hb
  have orth := orthonormal_iff_ite.mp B.orthonormal
  simp only [real_inner_smul_right,orth,if_pos rfl,if_neg hij,mul_one,mul_zero] at hh
  exact hne ((eigenvalue_detection r b ⟨(B j).ofLp,(WithLp.ofLp_eq_zero 2).ne.2 (B.orthonormal.ne_zero j)⟩
    _ hj).2.mp hh)

/-- Exact zero modes are weighted cancellations inside each equal-rate fibre. -/
theorem kernel_fibres (r b v : Fin n → ℝ) :
    (response r b).mulVec v = 0 ↔ ∀ t : ℝ, ∑ i ∈ univ.filter (fun i => rate r i = t), b i*v i = 0 := by
  classical
  constructor
  · intro hv t
    have vanish (w : Fin n → ℝ) (hw : (response r b).mulVec w = 0) : reading b w = 0 := by
      apply sq_eq_zero_iff.mp
      simpa only [zero_mul] using eigen_reading r b w 0 (by simpa using hw)
    have stable (s : Finset ℝ) :
        (response r b).mulVec (fun i => (∏ y ∈ s, (rate r i-y))*v i) = 0 := by
      induction s using Finset.induction_on with
      | empty => simpa using hv
      | insert a s ha ih =>
        funext i
        simp only [prod_insert ha,mul_assoc]
        rw [shifted_action,ih,vanish _ ih]
        simp
    let T := (univ.image (rate r)).erase t
    let K := ∏ y ∈ T, (t-y)
    have hn : K ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr
      (Finset.ne_of_mem_erase hy).symm
    have h := vanish _ (stable T)
    have he : reading b (fun i => (∏ y ∈ T, (rate r i-y))*v i) =
        K*∑ i ∈ univ.filter (fun i => rate r i=t), b i*v i := by
      rw [reading,Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hti : rate r i=t
      · simp [hti,K,mul_left_comm]
      · have hi : rate r i ∈ T := mem_erase.mpr ⟨hti,mem_image_of_mem _ (mem_univ _)⟩
        rw [if_neg hti,Finset.prod_eq_zero hi (sub_self _),zero_mul,mul_zero]
    exact (mul_eq_zero.mp (he ▸ h)).resolve_left hn
  · intro h
    funext i
    change (∑ j, response r b i j*v j) = 0
    let T := univ.image (rate r)
    have group := Finset.sum_fiberwise_of_maps_to
      (s := (univ : Finset (Fin n))) (t := T) (g := rate r)
      (fun j _ => mem_image_of_mem _ (mem_univ j)) (fun j => response r b i j*v j)
    rw [← group]
    apply Finset.sum_eq_zero
    intro t _
    have eq : (∑ j ∈ univ.filter (fun j => rate r j=t), response r b i j*v j) =
        (2*b i/(rate r i+t)) * ∑ j ∈ univ.filter (fun j => rate r j=t), b j*v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [response,(mem_filter.mp hj).2]
      ring
    rw [eq,h,mul_zero]

end GaloisForLFunctions.HilbertMetric.CauchySpectrum
