import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromSuccessiveLogWindows

/-!
# A uniformly conditioned bank of translations for logarithmic windows

The rotations of successive cutoff correlations can be chosen from a
single dyadic list for each cutoff. Each pair has a rotation in the
interval [π/4,π/2]. This gives a
uniform inverse for the imaginary part while keeping the largest time
shift linear in the number of coefficients.
-/

noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- The jth time shift, halved at each successive scale. -/
def dyadicShift (N j : ℕ) : ℝ := Real.pi*((N+1:ℕ):ℝ)/(4*2^j)

/-- Frequency-dependent index in the bank shared by the whole row. -/
def shiftIndex (N m : ℕ) := Nat.log 2 ⌊((N+1:ℕ):ℝ)*gap N m⌋₊

private theorem scaled_gap {N m : ℕ} (hm : m ∈ Icc 1 N) :
    1 ≤ ((N+1:ℕ):ℝ)*gap N m ∧ ((N+1:ℕ):ℝ)*gap N m ≤ (((N+1)^2:ℕ):ℝ) := by
  have hm' := mem_Icc.mp hm
  have hp : (0:ℝ) < (N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have h₁ := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le (Nat.succ_pos N) hm'.1
    (by omega : N+1 ≠ m) le_rfl (hm'.2.trans (Nat.le_succ N))
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hm'.1) (Nat.cast_le.mpr (hm'.2.trans (Nat.le_succ N)))
  rw [abs_of_nonneg (sub_nonneg.mpr hlog),← one_div] at h₁
  constructor
  · have h := (div_le_iff₀ hp).mp h₁
    rw [mul_comm] at h
    exact h
  · rw [Nat.cast_pow,sq]
    apply mul_le_mul_of_nonneg_left _ hp.le
    dsimp only [gap]
    linarith only [Real.log_le_sub_one_of_pos hp,Real.log_natCast_nonneg m]

/-- At most 1 + floor(log₂((N+1)²)) shifts are needed, and the chosen
angle for every log gap lies in [π/4,π/2]. -/
theorem dyadic_selection {N m : ℕ} (hm : m ∈ Icc 1 N) :
    shiftIndex N m ≤ Nat.log 2 ((N+1)^2) ∧
      dyadicShift N (shiftIndex N m)*gap N m ∈ Set.Icc (Real.pi/4) (Real.pi/2) := by
  let x := ((N+1:ℕ):ℝ)*gap N m
  have hx := scaled_gap hm
  have hx1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.1)
  let j := shiftIndex N m
  have hlo : (2:ℝ)^j ≤ x := by
    refine le_trans ?_ (Nat.floor_le (zero_le_one.trans hx.1))
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊x⌋₊ ≠ 0)
  have hhi : x < 2*(2:ℝ)^j := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) ⌊x⌋₊
    have hh : ((⌊x⌋₊+1:ℕ):ℝ) ≤ 2*(2:ℝ)^j := by
      rw [mul_comm,← pow_succ]
      exact_mod_cast Nat.succ_le_of_lt h
    exact (Nat.lt_floor_add_one x).trans_le (by simpa only [Nat.cast_add,Nat.cast_one] using hh)
  constructor
  · exact Nat.log_mono_right ((Nat.floor_mono hx.2).trans_eq (Nat.floor_natCast _))
  · change Real.pi/4 ≤ dyadicShift N j*gap N m ∧ dyadicShift N j*gap N m ≤ Real.pi/2
    have he : dyadicShift N j*gap N m = Real.pi*x/(4*2^j) := by dsimp only [dyadicShift,x]; ring
    rw [he]
    constructor
    · rw [le_div_iff₀ (by positivity)]
      linarith only [mul_le_mul_of_nonneg_left hlo Real.pi_pos.le]
    · rw [div_le_iff₀ (by positivity)]
      linarith only [mul_le_mul_of_nonneg_left hhi.le Real.pi_pos.le]

private theorem half_le_sine {N m : ℕ} (hm : m ∈ Icc 1 N) :
    1/2 ≤ Real.sin (dyadicShift N (shiftIndex N m)*gap N m) := by
  have h := (dyadic_selection hm).2
  rw [← Real.sin_pi_div_six]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [Real.pi_pos]) h.2
    (by linarith only [h.1,Real.pi_pos])

/-- The time aperture has optimal linear growth: at the adjacent frequency
every translation with sine at least δ costs at least δ n in absolute time. -/
theorem required_aperture {n : ℕ} (hn : 0<n) (t δ : ℝ)
    (h : δ ≤ |Real.sin (t*gap n n)|) : δ*n ≤ |t| :=
  (le_div_iff₀ (Nat.cast_pos.mpr hn)).mp (h.trans (adjacent_translation_bound t hn))

/-- Recover the imaginary part from untwisted and dyadically twisted real
measurements. This formula has a sine denominator bounded below by 1/2. -/
def demodulate (θ x v : ℝ) := (x*Real.cos θ-v)/Real.sin θ

theorem dyadic_read_imaginary (a : ℕ → ℂ) {N m : ℕ} (hm : m ∈ Icc 1 N) {h : ℝ}
    (hh : 0<h) (hcut : h ≤ ((N+1:ℕ):ℝ)⁻¹) :
    let t := dyadicShift N (shiftIndex N m)
    let g := gap N m
    demodulate (t*g) (second (row a N) g h/(2*h))
      (second (row (translated a t) N) g h/(2*h)) = (a (N+1)*conj (a m)).im := by
  intro t g
  have hs : Real.sin (t*g) ≠ 0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (half_le_sine hm)).ne'
  rw [read_gram a hm hh hcut,read_gram _ hm hh hcut,translated_gram,demodulate,div_eq_iff hs]
  dsimp only [g,gap]
  ring

/-- Noise in either extracted real correlation enters the imaginary
reconstruction with gain at most two, independently of the cutoff. -/
theorem dyadic_error {N m : ℕ} (hm : m ∈ Icc 1 N) (x v e f : ℝ) :
    let θ := dyadicShift N (shiftIndex N m)*gap N m
    |demodulate θ (x+e) (v+f)-demodulate θ x v| ≤ 2*(|e|+|f|) := by
  intro θ
  have hs : 1/2 ≤ Real.sin θ := half_le_sine hm
  have hp : 0<Real.sin θ := by linarith only [hs]
  rw [demodulate,demodulate,←sub_div,show (x+e)*Real.cos θ-(v+f)-(x*Real.cos θ-v)=e*Real.cos θ-f by ring,
    abs_div,abs_of_pos hp,div_le_iff₀ hp]
  have hcos := abs_sub (e*Real.cos θ) f
  rw [abs_mul] at hcos
  have hsmall := mul_le_of_le_one_right (abs_nonneg e) (abs_le.mpr ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)
  have hlarge := mul_le_mul_of_nonneg_left hs (add_nonneg (abs_nonneg e) (abs_nonneg f))
  linarith only [hcos,hsmall,hlarge]

/-- Six bandwidth samples from two neighboring cutoffs. -/
def extract (F : ℕ → ℝ → ℝ) (N : ℕ) (g h : ℝ) :=
  second (fun d => F (N+1) d-F N d) g h/(2*h)

/-- Error propagation from the six original energies, before demodulation. -/
theorem extraction_error (F G : ℕ → ℝ → ℝ) (N : ℕ) (g : ℝ) {h δ : ℝ} (hh : 0<h)
    (he : ∀ k ∈ ({N,N+1} : Finset ℕ), ∀ d ∈ ({g-h,g,g+h} : Finset ℝ),
      |F k d-G k d| ≤ δ) :
    |extract F N g h-extract G N g h| ≤ 4*δ/h := by
  classical
  have hs (d : ℝ) (hd : d ∈ ({g-h,g,g+h} : Finset ℝ)) :
      |(F (N+1) d-F N d)-(G (N+1) d-G N d)| ≤ 2*δ := by
    rw [show (F (N+1) d-F N d)-(G (N+1) d-G N d)=(F (N+1) d-G (N+1) d)-(F N d-G N d) by ring]
    exact (abs_sub _ _).trans (by linarith only [he (N+1) (by simp) d hd,he N (by simp) d hd])
  obtain ⟨ha,hb⟩ := abs_le.mp (hs (g-h) (by simp))
  obtain ⟨hc,hd⟩ := abs_le.mp (hs g (by simp))
  obtain ⟨hf,hg⟩ := abs_le.mp (hs (g+h) (by simp))
  rw [extract,extract,←sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*h),div_le_iff₀ (by positivity)]
  have hcanc : 4*δ/h*(2*h)=8*δ := by field_simp; ring
  rw [hcanc,abs_le]
  dsimp only [second]
  constructor <;> linarith only [ha,hb,hc,hd,hf,hg]

/-- End-to-end error on the imaginary part of the correlation when each
of the twelve input energy samples differs from the exact value by δ. -/
theorem raw_energy_error (a : ℕ → ℂ) {N m : ℕ} (hm : m ∈ Icc 1 N) {h δ : ℝ}
    (hh : 0<h) (hcut : h ≤ ((N+1:ℕ):ℝ)⁻¹) (F G : ℕ → ℝ → ℝ) :
    let t := dyadicShift N (shiftIndex N m)
    let g := gap N m
    (∀ k ∈ ({N,N+1} : Finset ℕ), ∀ d ∈ ({g-h,g,g+h} : Finset ℝ), |F k d-energy a k d| ≤ δ) →
    (∀ k ∈ ({N,N+1} : Finset ℕ), ∀ d ∈ ({g-h,g,g+h} : Finset ℝ),
      |G k d-energy (translated a t) k d| ≤ δ) →
    |demodulate (t*g) (extract F N g h) (extract G N g h) - (a (N+1)*conj (a m)).im| ≤ 16*δ/h := by
  intro t g hF hG
  let x := extract (energy a) N g h
  let v := extract (energy (translated a t)) N g h
  have hd : demodulate (t*g) x v=(a (N+1)*conj (a m)).im := dyadic_read_imaginary a hm hh hcut
  have hx := extraction_error F (energy a) N g hh hF
  have hv := extraction_error G (energy (translated a t)) N g hh hG
  have he := dyadic_error hm x v (extract F N g h-x) (extract G N g h-v)
  simp only [add_sub_cancel] at he
  rw [← hd]
  refine he.trans ?_
  have h4 : 16*δ/h = 4*(4*δ/h) := by ring
  change 2*(|extract F N g h-extract (energy a) N g h|+
      |extract G N g h-extract (energy (translated a t)) N g h|) ≤ _
  linarith only [hx,hv,h4]

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
