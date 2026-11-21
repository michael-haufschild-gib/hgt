import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AssociativeComposition

/-!
# Quantum amplitudes of nested outcome classes

Uniform normalization, agreement under refinement, and independent composition
determine the modulus of every class amplitude. All remaining freedom is a
completely multiplicative circle phase on the positive integers.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

/-- Singleton normalization, nested refinement, and independent product experiments. -/
def coherentRefinement (A : ℕ+ → ℕ+ → ℂ) : Prop :=
  (∀ n : ℕ+, ((n : ℕ) : ℝ) * ‖A 1 n‖^2 = 1) ∧
  (∀ i j k, i ≤ j → j ≤ k → A i j * A j k = A i k) ∧
  (∀ i j k l, i ≤ j → k ≤ l → A (i*k) (j*l) = A i j * A k l)

private def sizeRoot : ℕ+ →* ℂ where
  toFun n := (Real.sqrt (n : ℕ) : ℂ)
  map_one' := by norm_num
  map_mul' m n := by
    rw [PNat.mul_coe, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

private theorem sizeRoot_ne (n : ℕ+) : sizeRoot n ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast n.pos)).ne'

private theorem sizeRoot_norm_sq (n : ℕ+) : ‖sizeRoot n‖^2 = (n : ℕ) := by
  change ‖(Real.sqrt (n : ℕ) : ℂ)‖^2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Amplitude of one microscopic outcome. -/
def singletonAmplitude (χ : ℕ+ →* Circle) (n : ℕ+) : ℂ := (χ n : ℂ) / sizeRoot n

private theorem singleton_ne (χ : ℕ+ →* Circle) (n : ℕ+) : singletonAmplitude χ n ≠ 0 :=
  div_ne_zero (Circle.coe_ne_zero _) (sizeRoot_ne n)

private theorem singleton_one (χ : ℕ+ →* Circle) : singletonAmplitude χ 1 = 1 := by
  simp only [singletonAmplitude, map_one, Circle.coe_one, div_one]

private theorem singleton_mul (χ : ℕ+ →* Circle) (m n : ℕ+) :
    singletonAmplitude χ (m*n) = singletonAmplitude χ m * singletonAmplitude χ n := by
  simp only [singletonAmplitude, map_mul, Circle.coe_mul, div_mul_div_comm]

private theorem singleton_norm_sq (χ : ℕ+ →* Circle) (n : ℕ+) :
    ‖singletonAmplitude χ n‖^2 = 1 / ((n : ℕ) : ℝ) := by
  rw [singletonAmplitude, norm_div, div_pow, Circle.norm_coe, one_pow, sizeRoot_norm_sq]

/-- The amplitude of a class is the quotient of the two singleton amplitudes. -/
def refinementAmplitude (χ : ℕ+ →* Circle) (m n : ℕ+) :=
  singletonAmplitude χ n / singletonAmplitude χ m

theorem refinement_born_weight (χ : ℕ+ →* Circle) (m n : ℕ+) :
    ‖refinementAmplitude χ m n‖^2 = ((m : ℕ) : ℝ) / (n : ℕ) := by
  rw [refinementAmplitude, norm_div, div_pow, singleton_norm_sq, singleton_norm_sq]
  simp only [one_div, div_inv_eq_mul, div_eq_inv_mul]

private theorem vacuum_le (n : ℕ+) : (1 : ℕ+) ≤ n := n.pos

theorem refinementAmplitude_coherent (χ : ℕ+ →* Circle) : coherentRefinement (refinementAmplitude χ) := by
  refine ⟨fun n => ?_, fun i j k _ _ => ?_, fun i j k l _ _ => ?_⟩
  · rw [refinement_born_weight, PNat.coe_one, Nat.cast_one, mul_one_div_cancel (by exact_mod_cast n.ne_zero)]
  · unfold refinementAmplitude
    field_simp [singleton_ne]
  · simp only [refinementAmplitude, singleton_mul, div_mul_div_comm]

/-- The three experimental laws classify the amplitudes and determine their phase character uniquely. -/
theorem coherentRefinement_iff (A : ℕ+ → ℕ+ → ℂ) :
    coherentRefinement A ↔ ∃! χ : ℕ+ →* Circle,
      ∀ m n, m ≤ n → A m n = refinementAmplitude χ m n := by
  constructor
  · rintro ⟨hunit, hchain, hprod⟩
    let B (n : ℕ+) := A 1 n
    have hne (n : ℕ+) : B n ≠ 0 := by
      intro hz
      have h := hunit n
      change ((n : ℕ) : ℝ) * ‖B n‖^2 = 1 at h
      simp [hz] at h
    have hmul (m n : ℕ+) : B (m*n) = B m * B n := by
      simpa only [B, one_mul] using hprod 1 m 1 n (vacuum_le _) (vacuum_le _)
    have h1 : B 1 = 1 := by
      apply mul_left_cancel₀ (hne 1)
      simpa only [mul_one] using (hmul 1 1).symm
    let C (n : ℕ+) : Circle := ⟨B n * sizeRoot n, mem_sphere_zero_iff_norm.mpr (by
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [norm_mul, mul_pow, sizeRoot_norm_sq, one_pow, mul_comm]
      exact hunit n)⟩
    let χ : ℕ+ →* Circle := {
      toFun := C
      map_one' := Circle.ext (by change B 1 * sizeRoot 1 = 1; rw [h1, map_one, one_mul])
      map_mul' := fun m n => Circle.ext (by
        change B (m*n) * sizeRoot (m*n) = B m * sizeRoot m * (B n * sizeRoot n)
        rw [hmul, map_mul]
        ring) }
    have hχ (n : ℕ+) : singletonAmplitude χ n = B n := by
      change B n * sizeRoot n / sizeRoot n = B n
      exact mul_div_cancel_right₀ _ (sizeRoot_ne n)
    refine ⟨χ, ?_, ?_⟩
    · intro m n hmn
      rw [refinementAmplitude, hχ, hχ, eq_div_iff (hne _), mul_comm]
      exact hchain 1 m n (vacuum_le _) hmn
    · intro ψ hψ
      apply MonoidHom.ext
      intro n
      apply Circle.ext
      have he := hψ 1 n (vacuum_le n)
      rw [refinementAmplitude, singleton_one, div_one] at he
      have h : singletonAmplitude ψ n = singletonAmplitude χ n := he.symm.trans (hχ n).symm
      exact (div_left_inj' (sizeRoot_ne n)).mp h
  · rintro ⟨χ, hχ, _⟩
    obtain ⟨hu, hc, hp⟩ := refinementAmplitude_coherent χ
    refine ⟨fun n => ?_, fun i j k hij hjk => ?_, fun i j k l hij hkl => ?_⟩
    · rw [hχ 1 n (vacuum_le _)]
      exact hu n
    · rw [hχ i j hij, hχ j k hjk, hχ i k (hij.trans hjk)]
      exact hc _ _ _ hij hjk
    · rw [hχ _ _ (mul_le_mul' hij hkl), hχ i j hij, hχ k l hkl]
      exact hp _ _ _ _ hij hkl

/-- Born probabilities add to one for every finite partition with positive class sizes. -/
theorem partition_born_sum {ι : Type*} [Fintype ι] [Nonempty ι] (χ : ℕ+ →* Circle) (sizes : ι → ℕ+) :
    let total : ℕ+ := ⟨∑ i, (sizes i : ℕ),
      Finset.sum_pos (fun i _ => (sizes i).pos) Finset.univ_nonempty⟩
    ∑ i, ‖refinementAmplitude χ (sizes i) total‖^2 = 1 := by
  intro total
  simp only [refinement_born_weight, ← Finset.sum_div, ← Nat.cast_sum]
  exact div_self (by exact_mod_cast total.ne_zero)

/-- Relative heat amplitude of a class of m microscopic states in a shell of size n. -/
def heatRefinement (s : ℂ) (m n : ℕ+) := heat s n / heat s m

/-- The autonomous heat evolution satisfies all three refinement laws exactly on the critical line. -/
theorem heatRefinement_coherent_iff (s : ℂ) :
    coherentRefinement (heatRefinement s) ↔ s.re = 1/2 := by
  have h₁ : heat s 1 = 1 := by simp [heat, energy]
  have hne (n : ℕ+) : heat s n ≠ 0 := Complex.exp_ne_zero _
  have mass (n : ℕ+) : ((n : ℕ) : ℝ) * ‖heatRefinement s 1 n‖^2 = shellMass s n := by
    rw [heatRefinement, h₁, div_one, shellMass_eq]
  constructor
  · intro h
    have hv := h.1 2
    rw [mass, shellMass, Real.exp_eq_one_iff] at hv
    have he : 0 < energy 2 := Real.log_pos (by norm_num)
    have hz := (mul_eq_zero.mp hv).resolve_right he.ne'
    linarith
  · intro hs
    refine ⟨fun n => ?_, fun i j k _ _ => ?_, fun i j k l _ _ => ?_⟩
    · rw [mass]; simp [shellMass, hs]
    · unfold heatRefinement
      field_simp [hne]
    · simp only [heatRefinement, heat_mul, div_mul_div_comm]

/-- The associative divisor channel is the heat refinement of its microscopic state count. -/
theorem compositionAmplitude_eq_refinement (s : ℂ) (F G : Profile) (a b : ℕ+) :
    compositionAmplitude s F G a b = heatRefinement s
      ⟨F.val a * G.val b, Nat.mul_pos (F.property _ a.pos) (G.property _ b.pos)⟩
      ⟨(F*G).val ((a : ℕ)*(b : ℕ)), (F*G).property _ (Nat.mul_pos a.pos b.pos)⟩ := by
  have hf : (0 : ℝ) < F.val a := Nat.cast_pos.mpr (F.property _ a.pos)
  have hg : (0 : ℝ) < G.val b := Nat.cast_pos.mpr (G.property _ b.pos)
  simp only [compositionAmplitude, multiplicityPower, heatRefinement, heat, energy, Nat.cast_mul,
    Real.log_mul hf.ne' hg.ne', Complex.ofReal_add, mul_add, neg_mul, Complex.exp_neg,
    ← Complex.exp_add, inv_div_inv]

#print axioms refinement_born_weight
#print axioms refinementAmplitude_coherent
#print axioms coherentRefinement_iff
#print axioms partition_born_sum
#print axioms heatRefinement_coherent_iff
#print axioms compositionAmplitude_eq_refinement

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
