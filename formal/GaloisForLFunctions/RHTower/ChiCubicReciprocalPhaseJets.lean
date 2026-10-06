import GaloisForLFunctions.RHTower.ChiCubicNormalConjugation

/-!
# Uniform derivatives of the literal reciprocal phase

Every ordinary normalized derivative costs only N^n on the full fixed
cube. The real oscillation has unit-norm derivatives at every order;
compact geometric jets and the finite-order composition bound produce
the entire growing-parameter estimate. The reciprocal prefactor remains.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace RHTower.BAGTrace

private abbrev E := BAGPhysicalSpace
private def U : Set E := {v | 0 < v 2}
private def box : Set E := {v | ∀ i, v i ∈ Icc (1 : ℝ) 2}
private def geom (v : E) : ℝ := 2*Real.pi*v 0*v 1/v 2
private def recip (v : E) : ℂ := ((v 2)⁻¹ : ℝ)
private def osc (x : ℝ) : ℂ := Complex.exp ((x : ℂ)*Complex.I)

private theorem U_open : IsOpen U :=
  isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3)).continuous
private theorem box_U {v : E} (hv : v ∈ box) : v ∈ U := lt_of_lt_of_le zero_lt_one (hv 2).1
private theorem fin_le (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
private theorem box_compact : IsCompact box := by
  have he : box = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
      (Set.univ.pi (fun _ : Fin 3 => Icc (1 : ℝ) 2)) := by
    ext v
    change (∀ i, v i ∈ Icc (1 : ℝ) 2) ↔
      ∀ i ∈ (Set.univ : Set (Fin 3)), v i ∈ Icc (1 : ℝ) 2
    simp only [Set.mem_univ, forall_const]
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := (1 : ℝ)) (b := 2)))

private theorem geom_smooth : ContDiffOn ℝ ∞ geom U := by
  intro v hv
  have hp (i : Fin 3) : ContDiffAt ℝ ∞ (fun v : E => v i) v :=
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.contDiffAt
  exact (((contDiffAt_const.mul (hp 0)).mul (hp 1)).div (hp 2) (ne_of_gt hv)).contDiffWithinAt

private theorem recip_smooth : ContDiffOn ℝ ∞ recip U := by
  intro v hv
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp v
    ((EuclideanSpace.proj (2 : Fin 3) : E →L[ℝ] ℝ).contDiff.contDiffAt.inv
      (ne_of_gt hv))).contDiffWithinAt

private theorem osc_smooth : ContDiff ℝ ∞ osc :=
  (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

private theorem osc_deriv (x : ℝ) : HasDerivAt osc (Complex.I*osc x) x := by
  apply (((Complex.hasDerivAt_ofReal x).mul_const Complex.I).cexp).congr_deriv
  simp only [one_mul, osc]
  ring

private theorem osc_iterated (n : ℕ) : iteratedDeriv n osc = fun x => Complex.I^n*osc x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((osc_deriv x).const_mul (Complex.I^n)).deriv, pow_succ]
    ring

private theorem osc_jet_norm (n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ n osc x‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, osc_iterated]
  simp [osc, norm_pow, Complex.norm_exp]

private theorem fixed_jets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ box, ‖iteratedFDeriv ℝ n f v‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n f) box := by
    intro v hv
    exact ((hf.contDiffAt (U_open.mem_nhds (box_U hv))).continuousAt_iteratedFDeriv
      (fin_le n)).continuousWithinAt
  obtain ⟨C,hC⟩ := box_compact.exists_bound_of_continuousOn hc
  exact ⟨max C 0+1,by positivity,fun v hv => (hC v hv).trans (by linarith [le_max_left C 0])⟩

private theorem oscillatory_jets (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // 1 ≤ r}, ∀ v ∈ box,
      ‖iteratedFDeriv ℝ n (fun w => osc (N.1*geom w)) v‖ ≤ C*N.1^n := by
  choose B hB hBb using fixed_jets geom geom_smooth
  let A : ℝ := 1 + ∑ i ∈ Finset.range (n+1), B i
  have hA : 1 ≤ A := by
    have hs : 0 ≤ ∑ i ∈ Finset.range (n+1), B i := Finset.sum_nonneg (fun i _ => (hB i).le)
    dsimp only [A]
    linarith
  have hBA (i : ℕ) (hi : i ≤ n) : B i ≤ A := by
    have hs := Finset.single_le_sum (fun j _ => (hB j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact hs.trans (by dsimp only [A]; linarith)
  refine ⟨(n.factorial : ℝ)*A^n,mul_pos (by exact_mod_cast Nat.factorial_pos n)
    (pow_pos (lt_of_lt_of_le zero_lt_one hA) n),fun N v hv => ?_⟩
  have hN : 0 < N.1 := lt_of_lt_of_le zero_lt_one N.2
  have hf : ContDiffOn ℝ ∞ (fun w => N.1*geom w) U := contDiffOn_const.mul geom_smooth
  have hc (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i osc univ (N.1*geom v)‖ ≤ (1 : ℝ) := by
    rw [iteratedFDerivWithin_univ, osc_jet_norm]
  have hd (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (fun w => N.1*geom w) U v‖ ≤ (N.1*A)^i := by
    rw [iteratedFDerivWithin_of_isOpen i U_open (box_U hv)]
    change ‖iteratedFDeriv ℝ i (fun w => N.1 • geom w) v‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((geom_smooth.contDiffAt
      (U_open.mem_nhds (box_U hv))).of_le (fin_le i)), norm_smul,
      Real.norm_eq_abs, abs_of_pos hN]
    calc
      _ ≤ N.1*A := mul_le_mul_of_nonneg_left ((hBb i v hv).trans (hBA i hin)) hN.le
      _ ≤ (N.1*A)^i := le_self_pow₀ (by nlinarith [N.2, hA]) (by omega)
  have hb := norm_iteratedFDerivWithin_comp_le osc_smooth.contDiffOn hf (fin_le n)
    uniqueDiffOn_univ U_open.uniqueDiffOn (mapsTo_univ _ _) (box_U hv) hc hd
  rw [iteratedFDerivWithin_of_isOpen n U_open (box_U hv)] at hb
  simpa only [Function.comp_def, mul_pow, mul_one, mul_assoc, mul_comm, mul_left_comm] using hb

private theorem phase_eq (N : ℝ) : bagCubicNormalizedReciprocalPhase N =
    fun v => osc (N*geom v)*recip v := by
  funext v
  simp only [bagCubicNormalizedReciprocalPhase, osc, geom, recip, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, div_eq_mul_inv]
  congr 1
  congr 1
  ring

/-- Smoothness of the literal normalized reciprocal oscillation on positive height. -/
theorem bagCubicNormalizedReciprocalPhase_contDiffOn (N : ℝ) :
    ContDiffOn ℝ ∞ (bagCubicNormalizedReciprocalPhase N) {v : BAGPhysicalSpace | 0 < v 2} := by
  rw [phase_eq]
  exact (osc_smooth.comp_contDiffOn (contDiffOn_const.mul geom_smooth)).mul recip_smooth

/-- Every ordinary derivative of the actual normalized reciprocal phase
costs only its natural scale N^n, uniformly throughout the full cube. -/
theorem bagCubicNormalizedReciprocalPhase_uniform_jets (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // 1 ≤ r}, ∀ v : BAGPhysicalSpace,
      (∀ i, v i ∈ Icc (1 : ℝ) 2) →
        ‖iteratedFDeriv ℝ n (bagCubicNormalizedReciprocalPhase N.1) v‖ ≤ C*N.1^n := by
  choose A hA hAb using oscillatory_jets
  choose B hB hBb using fixed_jets recip recip_smooth
  let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n-i)).le)
  refine ⟨C+1,by positivity,fun N v hv => ?_⟩
  have hN : 0 < N.1 := lt_of_lt_of_le zero_lt_one N.2
  have ho : ContDiffOn ℝ ∞ (fun w => osc (N.1*geom w)) U :=
    osc_smooth.comp_contDiffOn (contDiffOn_const.mul geom_smooth)
  have hb := norm_iteratedFDerivWithin_mul_le ho recip_smooth U_open.uniqueDiffOn (box_U hv) (fin_le n)
  have he (j : ℕ) (F : E → ℂ) : iteratedFDerivWithin ℝ j F U v = iteratedFDeriv ℝ j F v :=
    iteratedFDerivWithin_of_isOpen j U_open (box_U hv)
  simp only [he] at hb
  rw [phase_eq]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i (fun w => osc (N.1*geom w)) v‖ *
        ‖iteratedFDeriv ℝ (n-i) recip v‖ := hb
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)*N.1^n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hoB := (hAb i N v hv).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ N.2 hin) (hA i).le)
      calc
        _ ≤ (n.choose i : ℝ)*(A i*N.1^n)*B (n-i) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hoB (Nat.cast_nonneg _)) (hBb (n-i) v hv)
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hA i).le (pow_nonneg hN.le n)))
        _ = _ := by ring
    _ = C*N.1^n := by rw [Finset.sum_mul]
    _ ≤ (C+1)*N.1^n := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hN.le n)

end RHTower.BAGTrace
