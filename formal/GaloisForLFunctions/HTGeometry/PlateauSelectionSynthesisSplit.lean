/-
# The plateau's selection--synthesis split

A continuous plateau of an autonomous orbit is a Lipschitz curve every point of which needs a long
gate word.  The mesh encoder therefore locates each point of the segment with at most the
logarithm of the mesh count in selection information, while the population of words it emits is
exponentially atypical for the geometrically killed local-gate prior.  The two currencies of the
gate cost separate on one ordinary trajectory.

Main results:
* `gateAct`, `wordAct_gateAct` — the gate alphabet acting on register states.
* `lt_wordComplexity_of_forall_notMem` — a depth-`S` circuit-ball miss is a complexity bound for
  words of *every* length at most `S`.
* `exists_plateau_codebook_split` — **the selection--synthesis split on a plateau segment**.
-/
import GaloisForLFunctions.HTGeometry.CurveCodebook
import GaloisForLFunctions.HTGeometry.EncoderSelectionInformation
import GaloisForLFunctions.HTGeometry.GateWordDictionary
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow
import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman
import GaloisForLFunctions.HTGeometry.WitnessWordDivergence

open Matrix MeasureTheory Set _root_.HTGeometry
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## The gate alphabet acting on register states -/

section GateAction

variable {I : Type} [Fintype I] [DecidableEq I] {Γ : Type*}

/-- One gate acting on a register state. -/
def gateAct (g : Γ → Matrix I I ℂ) : Γ → EuclideanSpace ℂ I → EuclideanSpace ℂ I :=
  fun c x => eucVec (g c *ᵥ (WithLp.ofLp x))

/-- A word of gates acts by the ordered product of its letters. -/
theorem wordAct_gateAct (g : Γ → Matrix I I ℂ) (psi : I → ℂ) :
    ∀ w : List Γ, wordAct (gateAct g) w (eucVec psi) = eucVec (((w.map g).prod) *ᵥ psi)
  | [] => by
      simp only [wordAct_nil, List.map_nil, List.prod_nil, Matrix.one_mulVec]
  | c :: w => by
      rw [wordAct_cons, wordAct_gateAct g psi w, gateAct]
      simp only [List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
      rfl

theorem gateWord_eq_prod_map (g : Γ → Matrix I I ℂ) {s : ℕ} (word : Fin s → Γ) :
    gateWord g word = ((List.ofFn word).map g).prod := by
  rw [gateWord, List.map_ofFn]
  rfl

/-- Every list of the right length is the tuple of some function. -/
theorem exists_ofFn_of_length_eq {w : List Γ} {s : ℕ} (h : w.length = s) :
    ∃ word : Fin s → Γ, List.ofFn word = w := by
  subst h
  exact ⟨w.get, List.ofFn_get w⟩

/-- **Padding.**  With the identity gate available, a word of length at most `s` has the same
action as a word of length exactly `s`. -/
theorem exists_length_eq_prod_map_eq {g : Γ → Matrix I I ℂ} {e : Γ} (he : g e = 1)
    {w : List Γ} {s : ℕ} (hw : w.length ≤ s) :
    ∃ word : Fin s → Γ, ((List.ofFn word).map g).prod = ((w.map g).prod) := by
  classical
  obtain ⟨w', hlen, hprod⟩ : ∃ w' : List Γ, w'.length = s ∧ ((w'.map g).prod) = ((w.map g).prod) := by
    refine ⟨List.replicate (s - w.length) e ++ w, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate]
      omega
    · rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, he, one_pow,
        one_mul]
  obtain ⟨word, hword⟩ := exists_ofFn_of_length_eq hlen
  exact ⟨word, by rw [hword, hprod]⟩

/-- **A depth-`S` circuit-ball miss bounds the complexity of every shorter word.** -/
theorem lt_wordComplexity_of_forall_notMem {g : Γ → Matrix I I ℂ} {e : Γ} (he : g e = 1)
    {psi : I → ℂ} {eps : ℝ} {S : ℕ} {x : EuclideanSpace ℂ I}
    (hne : ∃ w : List Γ, dist (wordAct (gateAct g) w (eucVec psi)) x ≤ eps)
    (hx : ∀ word : Fin S → Γ, ¬ dist x (eucVec (wordState g psi word)) ≤ eps) :
    S < wordComplexity (fun w => wordAct (gateAct g) w (eucVec psi)) eps x := by
  classical
  by_contra hcon
  push Not at hcon
  set endpoint : List Γ → EuclideanSpace ℂ I :=
    fun w => wordAct (gateAct g) w (eucVec psi) with hend
  have hnee : {l : ℕ | ∃ w : List Γ, w.length = l ∧ Qualifies endpoint eps x w}.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hwlen, hwq⟩ : ∃ w : List Γ, w.length = wordComplexity endpoint eps x ∧
      Qualifies endpoint eps x w := Nat.sInf_mem hnee
  obtain ⟨word, hword⟩ := exists_length_eq_prod_map_eq he (w := w) (s := S) (by omega)
  refine hx word ?_
  have hval : eucVec (wordState g psi word) = endpoint w := by
    show eucVec (wordState g psi word) = wordAct (gateAct g) w (eucVec psi)
    rw [wordAct_gateAct, wordState, gateWord_eq_prod_map, hword]
  rw [hval, dist_comm]
  exact hwq

end GateAction


/-! ## The split on a plateau segment -/

section Split

variable {I : Type} [Fintype I] [DecidableEq I]
variable {Γ : Type} [Fintype Γ] [Encodable Γ]
variable [MeasurableSpace (List Γ)] [MeasurableSingletonClass (List Γ)]

/-- **`(23)`--`(24)`.**  On a continuous plateau segment of an autonomous orbit the mesh encoder
locates every point with at most `log N` nats of selection information, where `N` is the mesh
count, while the population of words it emits pays a synthesis divergence of at least the gate
cost of the plateau depth minus that same `log N`. -/
theorem exists_plateau_codebook_split
    {g : Γ → Matrix I I ℂ} {e : Γ} (he : g e = 1)
    {H : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {v : ℝ} (hv : 0 < v) (hHv : ‖H‖ ≤ v)
    {eps delta : ℝ} (hdelta : 0 < delta)
    (hfin : ∀ t : ℝ, ∃ w : List Γ,
      dist (wordAct (gateAct g) w (eucVec psi)) (orbitVec H psi t) ≤ eps)
    {S : ℕ} {t₀ W : ℝ} (hW : 0 < W)
    (hhard : ∀ u ∈ Set.Icc t₀ (t₀ + W),
      u ∉ metricEasySet H psi (eps + delta) (fun word : Fin S → Γ => wordState g psi word))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ) :
    ∃ (code : ℝ → List Γ) (cb : Finset (List Γ)),
      cb.card ≤ plateauGridCount W (delta / v) ∧ 0 < cb.card ∧
      HasSum (encoderLaw (windowProbabilityMeasure W : Measure ℝ) code) 1 ∧
      selectionInfo (windowProbabilityMeasure W : Measure ℝ) code ≤ Real.log (cb.card : ℝ) ∧
      ((S : ℝ) + 1) * Real.log ((Fintype.card Γ : ℝ) / a) - Real.log (cb.card : ℝ)
          - Real.log (1 - a)
        ≤ relEntropy (encoderLaw (windowProbabilityMeasure W : Measure ℝ) code)
            (wordPrior a) := by
  classical
  haveI : IsProbabilityMeasure (windowProbabilityMeasure W : Measure ℝ) :=
    (windowProbabilityMeasure W).2
  obtain ⟨endpoint, hend⟩ : ∃ f : List Γ → EuclideanSpace ℂ I,
    f = fun w => wordAct (gateAct g) w (eucVec psi) := ⟨_, rfl⟩
  obtain ⟨gamma, hgamma⟩ : ∃ f : ℝ → EuclideanSpace ℂ I,
    f = fun τ => orbitVec H psi (t₀ + τ) := ⟨_, rfl⟩
  have hlip : ∀ s t : ℝ, dist (gamma s) (gamma t) ≤ v * |s - t| := by
    intro s t
    rw [hgamma]
    have := dist_orbitVec_le hH hpsi hHv (t₀ + s) (t₀ + t)
    simpa using this
  have hfin' : ∀ t ∈ Set.Icc (0 : ℝ) W, ∃ w, Qualifies endpoint eps (gamma t) w := by
    intro t _
    obtain ⟨w, hw⟩ := hfin (t₀ + t)
    exact ⟨w, by rw [hend, hgamma]; exact hw⟩
  obtain ⟨code, cb, hcard, hmeas, hmem, -, hlenle⟩ :=
    exists_curve_codebook endpoint gamma hv hdelta hlip hfin'
  obtain ⟨q, hqdef⟩ : ∃ q : List Γ → ℝ,
    q = encoderLaw (windowProbabilityMeasure W : Measure ℝ) code := ⟨_, rfl⟩
  have hq0 : ∀ w, 0 ≤ q w := by
    intro w
    rw [hqdef, encoderLaw]
    exact measureReal_nonneg
  have hqsum : HasSum q 1 := by
    rw [hqdef]
    exact hasSum_encoderLaw _ code hmeas
  have hwindow : ∀ A : Set ℝ, (windowProbabilityMeasure W : Measure ℝ) A
      = (ENNReal.ofReal W)⁻¹ * volume (A ∩ Set.Ioc 0 W) := by
    intro A
    rw [windowProb_apply, windowLength, if_pos hW, Measure.restrict_apply' measurableSet_Ioc]
  have hsupp : ∀ w, w ∉ (↑cb : Set (List Γ)) → q w = 0 := by
    intro w hw
    have hempty : code ⁻¹' {w} ∩ Set.Ioc 0 W = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun t ht => ?_
      have hmemcb : code t ∈ cb := hmem t ⟨le_of_lt ht.2.1, ht.2.2⟩
      have : code t = w := ht.1
      rw [this] at hmemcb
      exact hw hmemcb
    rw [hqdef, encoderLaw, measureReal_def, hwindow, hempty]
    simp
  have hcardpos : 0 < cb.card := by
    refine Finset.card_pos.mpr ⟨code (W / 2), hmem (W / 2) ⟨by positivity, by linarith⟩⟩
  have hlong : ∀ w, q w ≠ 0 → S + 1 ≤ w.length := by
    intro w hw
    have hne : (code ⁻¹' {w} ∩ Set.Ioc 0 W).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      apply hw
      rw [hqdef, encoderLaw, measureReal_def, hwindow, hcon]
      simp
    obtain ⟨t, htw, htI⟩ := hne
    have htIcc : t ∈ Set.Icc (0 : ℝ) W := ⟨le_of_lt htI.1, htI.2⟩
    have hcodew : code t = w := htw
    have hne' : ∃ u : List Γ,
        dist (wordAct (gateAct g) u (eucVec psi)) (gamma t) ≤ eps + delta := by
      obtain ⟨u, hu⟩ := hfin (t₀ + t)
      exact ⟨u, by rw [hgamma]; linarith [hu]⟩
    have hx : ∀ word : Fin S → Γ,
        ¬ dist (gamma t) (eucVec (wordState g psi word)) ≤ eps + delta := by
      intro word hcon
      refine hhard (t₀ + t) ⟨by linarith [htIcc.1], by linarith [htIcc.2]⟩ ⟨word, ?_⟩
      rw [hgamma] at hcon
      exact hcon
    have hlt : S < wordComplexity endpoint (eps + delta) (gamma t) := by
      rw [hend]
      exact lt_wordComplexity_of_forall_notMem he hne' hx
    have hle := hlenle t htIcc
    rw [hcodew] at hle
    omega
  have hzero : ∀ (f : List Γ → ℝ), (∀ w, w ∉ cb → q w * f w = 0) →
      Summable fun w => q w * f w := by
    intro f hf
    exact summable_of_ne_finset_zero hf
  have hsum1 : Summable fun w => q w * (w.length : ℝ) :=
    hzero _ fun w hw => by rw [hsupp w (by simpa using hw), zero_mul]
  have hsum2 : Summable fun w => q w * Real.log (q w) :=
    hzero _ fun w hw => by rw [hsupp w (by simpa using hw), zero_mul]
  have hsum3 : Summable fun w => q w * Real.log (q w /
      condLaw (fun _ : List Γ => (1 : ℝ)) (↑cb : Set (List Γ)) (cb.card : ℝ) w) :=
    hzero _ fun w hw => by rw [hsupp w (by simpa using hw), zero_mul]
  have hsum4 : Summable fun w => q w * Real.log (q w / wordPrior a w) :=
    hzero _ fun w hw => by rw [hsupp w (by simpa using hw), zero_mul]
  refine ⟨code, cb, hcard, hcardpos, by rw [← hqdef]; exact hqsum, ?_, ?_⟩
  · rw [selectionInfo_eq_entropy, ← hqdef]
    exact entropy_le_log_card cb hcardpos hq0 hsupp hqsum hsum2 hsum3
  · rw [← hqdef]
    have := le_relEntropy_wordPrior_of_codebook (Γ := Γ) ha ha1 hM (S := S + 1) cb hcardpos
      hq0 hsupp hlong hqsum hsum1 hsum2 hsum3 hsum4
    push_cast at this
    exact this

end Split


/-! ## The two rows of the separation -/

section Rows

variable {I : Type} [Fintype I] [DecidableEq I]
variable {Γ : Type} [Fintype Γ] [Encodable Γ] [Nonempty Γ]
variable [MeasurableSpace (List Γ)] [MeasurableSingletonClass (List Γ)]

/-- **The split at arbitrarily late windows of an autonomous orbit.**  A Hamiltonian with a
maximally projective spectrum whose seed has small spectral collision has, beyond every horizon, a
window of length `W` on which the depth-`S` circuit ball is missed; on that window the mesh encoder
pays at most `log N` in selection information and at least the gate cost of `S+1` minus `log N` in
synthesis divergence. -/
theorem exists_late_plateau_codebook_split
    {g : Γ → Matrix I I ℂ} {ident : Γ} (he : g ident = 1)
    (hg : ∀ c, g c ∈ Matrix.unitaryGroup I ℂ)
    {H : Matrix I I ℂ} {ebasis : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H ebasis lam) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {eps delta : ℝ} (heps : 0 ≤ eps) (hdelta : 0 < delta)
    (hfin : ∀ t : ℝ, ∃ w : List Γ,
      dist (wordAct (gateAct g) w (eucVec psi)) (orbitVec H psi t) ≤ eps)
    {epsw : ℝ} (hgap : eps + delta < epsw) (hepsw : epsw < 1)
    {v : ℝ} (hv : 0 < v) (hHv : ‖H‖ ≤ v)
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖eigenCoords ebasis psi j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {S : ℕ} (hGamma : (Fintype.card Γ : ℝ) ≤ M)
    (hs : ((S : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    {W : ℝ} (hW : 0 < W)
    (hgrid : ((plateauGridCount W ((epsw - (eps + delta)) / v) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((r : ℝ) / 2)) < 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (A : ℝ) :
    ∃ t₀ : ℝ, A < t₀ ∧ ∃ (code : ℝ → List Γ) (cb : Finset (List Γ)),
      cb.card ≤ plateauGridCount W (delta / v) ∧ 0 < cb.card ∧
      HasSum (encoderLaw (windowProbabilityMeasure W : Measure ℝ) code) 1 ∧
      selectionInfo (windowProbabilityMeasure W : Measure ℝ) code ≤ Real.log (cb.card : ℝ) ∧
      ((S : ℝ) + 1) * Real.log ((Fintype.card Γ : ℝ) / a) - Real.log (cb.card : ℝ)
          - Real.log (1 - a)
        ≤ relEntropy (encoderLaw (windowProbabilityMeasure W : Measure ℝ) code)
            (wordPrior a) := by
  classical
  have hM0 : 0 < Fintype.card Γ := Fintype.card_pos
  have hZ : ∀ word : Fin S → Γ,
      finiteComplexInner (wordState g psi word) (wordState g psi word) = 1 :=
    fun word => finiteComplexInner_wordState_self hg hpsi word
  obtain ⟨t₀, ht₀, hhard⟩ := exists_late_hardWindow heb hmax ref hH hpsi
    (Z := fun word : Fin S → Γ => wordState g psi word) hZ
    (by linarith : (0 : ℝ) ≤ eps + delta) hgap hepsw hv hHv hr hcoll hscale hM
    (card_wordIndex_le_pow hGamma (le_of_lt hM) S) hs W hgrid A
  exact ⟨t₀, ht₀, exists_plateau_codebook_split he hH hpsi hv hHv hdelta hfin hW hhard ha ha1 hM0⟩

/-- The word law of a constant encoder is the point mass at that word. -/
theorem encoderLaw_const {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] (w₀ : List Γ) :
    encoderLaw mu (fun _ : X => w₀) = pointLaw w₀ := by
  funext w
  by_cases h : w = w₀
  · subst h
    have : (fun _ : X => w) ⁻¹' {w} = Set.univ := by
      ext x
      simp
    rw [encoderLaw, this, pointLaw, if_pos rfl, probReal_univ]
  · have : (fun _ : X => w₀) ⁻¹' {w} = (∅ : Set X) := by
      ext x
      simp [Ne.symm h]
    rw [encoderLaw, this, pointLaw, if_neg h]
    simp

/-- **`(25)` and the second row of `(26)`.**  One fixed preparation word carries no selection
information and pays exactly the surprisal of its own length in synthesis divergence. -/
theorem recurrence_row {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (w₀ : List Γ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ) :
    selectionInfo mu (fun _ : X => w₀) = 0 ∧
      relEntropy (encoderLaw mu (fun _ : X => w₀)) (wordPrior a)
        = -Real.log (1 - a) + (w₀.length : ℝ) * Real.log ((Fintype.card Γ : ℝ) / a) := by
  rw [selectionInfo_eq_entropy, encoderLaw_const]
  exact ⟨entropy_pointLaw w₀, relEntropy_pointLaw_wordPrior ha ha1 hM w₀⟩

end Rows

end GaloisForLFunctions.HTGeometry

end
