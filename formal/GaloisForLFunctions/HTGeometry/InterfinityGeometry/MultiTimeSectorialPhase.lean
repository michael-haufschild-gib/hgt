import GaloisForLFunctions.HTGeometry.InterfinityGeometry.MultiTimeTensorFinitePart
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralComplexDeficient

/-!
# The tensor sectorial limit and the conormal phase

The tensor finite part of `d` independent times, normalized by `∏_j R_j^{a_j}`, converges along
every product of rays of the right half-plane to the tensor terminal residue

`c ∏_j Γ(a_j) w_j^{-a_j} h_j(0)`.

Along the rays `w_j = e^{iθ_j}` the residue carries the phase `−∑_j a_j θ_j`, whose differential is
the conormal covector `−a`; its `j`-th component is the inward distance `−a_j = −β_j − ρ_j` to the
`j`-th death face.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology Complex

noncomputable section

variable {d : ℕ}

/-- The transported tensor finite part at complex times. -/
def ctensorFinitePart (c : ℝ) (a : Fin d → ℝ) (z : Fin d → ℂ) (h : Fin d → (ℝ → ℝ)) : ℂ :=
  (c : ℂ) * ∏ j, ctransportedFinitePart 1 (a j) (z j) (h j)

/-! ## The tensor sectorial limit -/

/-- **The tensor sectorial projective limit.** -/
theorem tendsto_ctensorFinitePart (c : ℝ) {a : Fin d → ℝ} (ha : ∀ j, -1 < a j)
    (ha0 : ∀ j, a j < 0) {w : Fin d → ℂ} (hw : ∀ j, 0 < (w j).re) {h : Fin d → (ℝ → ℝ)}
    (hh : ∀ j, IsSmoothReal (h j)) :
    Tendsto (fun R : Fin d → ℝ => (∏ j, ((R j ^ a j : ℝ) : ℂ)) *
        ctensorFinitePart c a (fun j => (R j : ℂ) * w j) h)
      (Filter.pi fun _ : Fin d => atTop)
      (𝓝 ((c : ℂ) * ∏ j, ((Real.Gamma (a j) : ℂ) * w j ^ ((-(a j) : ℝ) : ℂ) * (h j 0 : ℂ)))) := by
  have hfac : ∀ j : Fin d, Tendsto
      (fun R : Fin d → ℝ => ((R j ^ a j : ℝ) : ℂ) *
        ctransportedFinitePart 1 (a j) ((R j : ℂ) * w j) (h j))
      (Filter.pi fun _ : Fin d => atTop)
      (𝓝 ((Real.Gamma (a j) : ℂ) * w j ^ ((-(a j) : ℝ) : ℂ) * (h j 0 : ℂ))) := by
    intro j
    have hproj : Tendsto (fun R : Fin d → ℝ => R j) (Filter.pi fun _ : Fin d => atTop) atTop :=
      tendsto_eval_pi (fun _ : Fin d => (atTop : Filter ℝ)) j
    have hone := tendsto_ctransportedFinitePart 1 (ha j) (ha0 j) (hw j) (hh j)
    rw [Complex.ofReal_one, one_mul] at hone
    exact hone.comp hproj
  have hprod : Tendsto (fun R : Fin d → ℝ => ∏ j, (((R j ^ a j : ℝ) : ℂ) *
      ctransportedFinitePart 1 (a j) ((R j : ℂ) * w j) (h j)))
      (Filter.pi fun _ : Fin d => atTop)
      (𝓝 (∏ j, ((Real.Gamma (a j) : ℂ) * w j ^ ((-(a j) : ℝ) : ℂ) * (h j 0 : ℂ)))) :=
    tendsto_finsetProd _ fun j _ => hfac j
  have hres := hprod.const_mul (c : ℂ)
  refine hres.congr fun R => ?_
  rw [ctensorFinitePart, Finset.prod_mul_distrib]
  ring

/-- **The tensor terminal residue along a product of rays.** -/
theorem tendsto_ctensorFinitePart_ray (c : ℝ) {a : Fin d → ℝ} (ha : ∀ j, -1 < a j)
    (ha0 : ∀ j, a j < 0) {θ : Fin d → ℝ} (hθ1 : ∀ j, -(Real.pi / 2) < θ j)
    (hθ2 : ∀ j, θ j < Real.pi / 2) {h : Fin d → (ℝ → ℝ)} (hh : ∀ j, IsSmoothReal (h j)) :
    Tendsto (fun R : Fin d → ℝ => (∏ j, ((R j ^ a j : ℝ) : ℂ)) *
        ctensorFinitePart c a (fun j => (R j : ℂ) * Complex.exp ((θ j : ℂ) * Complex.I)) h)
      (Filter.pi fun _ : Fin d => atTop)
      (𝓝 ((c : ℂ) * ∏ j, ((Real.Gamma (a j) : ℂ) *
        Complex.exp (((-(a j * θ j) : ℝ) : ℂ) * Complex.I) * (h j 0 : ℂ)))) := by
  have hre : ∀ j : Fin d, (Complex.exp ((θ j : ℂ) * Complex.I)).re = Real.cos (θ j) := by
    intro j
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have hw : ∀ j : Fin d, 0 < (Complex.exp ((θ j : ℂ) * Complex.I)).re := by
    intro j
    rw [hre j]
    exact Real.cos_pos_of_mem_Ioo ⟨hθ1 j, hθ2 j⟩
  have hmain := tendsto_ctensorFinitePart c ha ha0 hw hh
  have hcpow : ∀ j : Fin d, (Complex.exp ((θ j : ℂ) * Complex.I)) ^ ((-(a j) : ℝ) : ℂ) =
      Complex.exp (((-(a j * θ j) : ℝ) : ℂ) * Complex.I) := by
    intro j
    have hp := Real.pi_pos
    have hlow : -Real.pi < θ j := by have := hθ1 j; linarith
    have hhigh : θ j ≤ Real.pi := by have := hθ2 j; linarith
    exact cpow_exp_mul_I (a j) hlow hhigh
  have hcongr : (∏ j, ((Real.Gamma (a j) : ℂ) *
      (Complex.exp ((θ j : ℂ) * Complex.I)) ^ ((-(a j) : ℝ) : ℂ) * (h j 0 : ℂ))) =
      ∏ j, ((Real.Gamma (a j) : ℂ) *
        Complex.exp (((-(a j * θ j) : ℝ) : ℂ) * Complex.I) * (h j 0 : ℂ)) :=
    Finset.prod_congr rfl fun j _ => by rw [hcpow j]
  rwa [hcongr] at hmain

/-! ## The conormal phase covector -/

/-- The total terminal phase of a tensor observer. -/
def terminalPhase (a θ : Fin d → ℝ) : ℝ := -∑ j, a j * θ j

/-- The terminal phase covector. -/
def phaseCovector (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  -∑ j, (a j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)

theorem phaseCovector_apply (a u : Fin d → ℝ) : phaseCovector a u = terminalPhase a u := by
  rw [phaseCovector, terminalPhase]
  simp

/-- **The phase differential is the conormal covector.** -/
theorem hasFDerivAt_terminalPhase (a θ : Fin d → ℝ) :
    HasFDerivAt (fun u : Fin d → ℝ => terminalPhase a u) (phaseCovector a) θ := by
  have hlin := (phaseCovector a).hasFDerivAt (x := θ)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards with u
  exact (phaseCovector_apply a u).symm

/-- **The `j`-th conormal component is the inward distance to the `j`-th death face.** -/
theorem phaseCovector_single (a : Fin d → ℝ) (j : Fin d) :
    phaseCovector a (Pi.single j 1) = -(a j) := by
  rw [phaseCovector_apply, terminalPhase]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem phaseCovector_single_eq_deficit (β ρ : Fin d → ℝ) (j : Fin d) :
    phaseCovector (fun i => ρ i + β i) (Pi.single j 1) = -β j - ρ j := by
  rw [phaseCovector_single]
  ring

/-! ## The angular slope in one coordinate -/

theorem terminalPhase_update (a θ : Fin d → ℝ) (j : Fin d) (u : ℝ) :
    terminalPhase a (Function.update θ j u) =
      -(a j * u) - ∑ i ∈ Finset.univ \ {j}, a i * θ i := by
  classical
  rw [terminalPhase, Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ j)]
  have hother : ∀ i ∈ Finset.univ \ ({j} : Finset (Fin d)),
      a i * Function.update θ j u i = a i * θ i := by
    intro i hi
    have hij : i ≠ j := by simpa using (Finset.mem_sdiff.1 hi).2
    rw [Function.update_of_ne hij]
  rw [Finset.sum_congr rfl hother, Function.update_self]
  ring

theorem hasDerivAt_terminalPhase_coord (a θ : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun u : ℝ => terminalPhase a (Function.update θ j u)) (-(a j)) (θ j) := by
  classical
  have hbase : HasDerivAt
      (fun u : ℝ => -(a j * u) - ∑ i ∈ Finset.univ \ ({j} : Finset (Fin d)), a i * θ i)
      (-(a j)) (θ j) := by
    have h0 : HasDerivAt (fun u : ℝ => a j * u) (a j) (θ j) := by
      simpa using (hasDerivAt_id (θ j)).const_mul (a j)
    simpa using h0.neg.sub_const (∑ i ∈ Finset.univ \ ({j} : Finset (Fin d)), a i * θ i)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards with u
  exact terminalPhase_update a θ j u

/-! ## The phase of the tensor residue -/

theorem multi_phase_prod (a θ : Fin d → ℝ) :
    (∏ j, Complex.exp (((-(a j * θ j) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((terminalPhase a θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, terminalPhase]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]

theorem arg_terminalPhase (a θ : Fin d → ℝ) (h1 : -Real.pi < terminalPhase a θ)
    (h2 : terminalPhase a θ ≤ Real.pi) :
    Complex.arg (∏ j, Complex.exp (((-(a j * θ j) : ℝ) : ℂ) * Complex.I)) = terminalPhase a θ := by
  rw [multi_phase_prod a θ]
  exact arg_terminal_phase h1 h2

/-- **The angular slope of the tensor residue in one coordinate is `−a_j`.** -/
theorem hasDerivAt_multi_terminal_arg (a θ : Fin d → ℝ) (j : Fin d)
    (h1 : -Real.pi < terminalPhase a θ) (h2 : terminalPhase a θ < Real.pi) :
    HasDerivAt (fun u : ℝ => Complex.arg (∏ i, Complex.exp
      (((-(a i * Function.update θ j u i) : ℝ) : ℂ) * Complex.I))) (-(a j)) (θ j) := by
  classical
  refine (hasDerivAt_terminalPhase_coord a θ j).congr_of_eventuallyEq ?_
  have hcont : Continuous fun u : ℝ => terminalPhase a (Function.update θ j u) := by
    have hEq : (fun u : ℝ => terminalPhase a (Function.update θ j u)) =
        fun u : ℝ => -(a j * u) - ∑ i ∈ Finset.univ \ ({j} : Finset (Fin d)), a i * θ i :=
      funext fun u => terminalPhase_update a θ j u
    rw [hEq]
    fun_prop
  have hopen : IsOpen {u : ℝ | |terminalPhase a (Function.update θ j u)| < Real.pi} :=
    isOpen_lt (continuous_abs.comp hcont) continuous_const
  have hmem : θ j ∈ {u : ℝ | |terminalPhase a (Function.update θ j u)| < Real.pi} := by
    simp only [mem_setOf_eq, Function.update_eq_self]
    exact abs_lt.2 ⟨h1, h2⟩
  filter_upwards [hopen.mem_nhds hmem] with u hu
  have hu' := abs_lt.1 hu
  exact arg_terminalPhase a (Function.update θ j u) hu'.1 hu'.2.le

end

end GaloisForLFunctions.HTGeometry.Interfinity
