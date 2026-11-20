import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromWideWindowSlopes
import GaloisForLFunctions.HTGeometry.KernelOfDimensionDrop
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Optimal fixed shifts for reading one more complex coefficient

When the first n coefficients are known, a late log window measures the
squared distance of the last coefficient to one point in the complex plane.
The Vandermonde argument for separated frequencies (Gabet–Ferreira Da
Costa–Lee, §4) gives a deterministic grid of 2n+1 measurements that works
for every nonzero reference prefix. For any prescribed 2n shifts there is
a nonzero reference prefix for which two distinct coefficients coincide in
all the measurements.
-/
noncomputable section
open Complex Finset Filter
open scoped ComplexConjugate Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
namespace LastCoefficient

/-- Rotation relative to the newly added site n+1. -/
def gap {n : ℕ} (i : Fin n) : ℝ := Real.log (n+1:ℕ)-Real.log (i.val+1:ℕ)
private def wave (u : ℝ) := cexp ((u:ℂ)*I)
private theorem wave_add (u v : ℝ) : wave (u+v)=wave u*wave v := by
  simp only [wave,Complex.ofReal_add,add_mul,Complex.exp_add]
private theorem conj_wave (u : ℝ) : conj (wave u)=wave (-u) := by
  simp [wave,←Complex.exp_conj]
private theorem wave_norm (u : ℝ) : ‖wave u‖=1 := by simp [wave,Complex.norm_exp]
private theorem wave_mul_nat (u : ℝ) (k : ℕ) : wave (k*u)=wave u^k := by
  simp only [wave,Complex.ofReal_mul,Complex.ofReal_natCast,mul_assoc,Complex.exp_nat_mul]

private theorem gap_pos {n : ℕ} (i : Fin n) : 0<gap i :=
  sub_pos.mpr (Real.log_lt_log (by positivity) (by exact_mod_cast Nat.add_lt_add_right i.isLt 1))
private theorem gap_injective (n : ℕ) : Function.Injective (gap (n:=n)) := by
  intro i j he
  have h : Real.log (i.val+1:ℕ)=Real.log (j.val+1:ℕ) :=
    sub_right_inj.mp he
  exact Fin.ext (Nat.add_right_cancel (by exact_mod_cast
    (Real.log_injOn_pos (by positivity) (by positivity) h)))
private theorem gap_le {n : ℕ} (i : Fin n) : gap i ≤ Real.log (n+1:ℕ) :=
  sub_le_self _ (Real.log_natCast_nonneg _)

private def reference {n : ℕ} (u : Fin n → ℂ) (t : ℝ) :=
  ∑ i, u i*wave (-t*gap i)

/-- Squared amplitude after adding z to a prefix u and dividing by the unit
phase of its last site. -/
def lastReading {n : ℕ} (u : Fin n → ℂ) (z : ℂ) (t : ℝ) := ‖z+reference u t‖^2

/-- These squared distances are the wide-window slopes of the original
translated coefficient sequence. -/
theorem last_reading_from_log_windows (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    Tendsto (fun d : ℝ => energy (translated a t) (n+1) d/d) atTop
      (𝓝 (lastReading (fun i : Fin n => a (i.val+1)) (a (n+1)) t)) := by
  let W := wave (t * Real.log (n+1:ℕ))
  have hW : ‖W‖=1 := wave_norm _
  have hsite (i : Fin n) : translated a t (i.val+1) =
      W*(a (i.val+1)*wave (-t*gap i)) := by
    have he : t*Real.log (i.val+1:ℕ)=t*Real.log (n+1:ℕ)+(-t*gap i) := by
      unfold gap; ring
    change a (i.val+1)*wave (t*Real.log (i.val+1:ℕ))=_
    rw [he,wave_add]; dsimp only [W]; ring
  have hprefix : (∑ k∈Icc 1 (n+1),translated a t k) =
      W*(a (n+1)+reference (fun i : Fin n => a (i.val+1)) t) := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1),
      RHTower.sum_Icc_eq_sum_range_shift,←Fin.sum_univ_eq_sum_range]
    simp_rw [hsite,←mul_sum]
    change W*reference (fun i : Fin n => a (i.val+1)) t+a (n+1)*W = _
    ring
  simpa only [hprefix,norm_mul,hW,one_mul,lastReading] using wide_window_slope (translated a t) (n+1)

private abbrev Index (n : ℕ) := Option (Fin n ⊕ Fin n)
private def freq {n : ℕ} : Index n → ℝ
  | none => 0
  | some (.inl i) => -gap i
  | some (.inr i) => gap i
private def mass {n : ℕ} (u : Fin n → ℂ) (x y : ℂ) : Index n → ℂ
  | none => ((‖x‖^2-‖y‖^2:ℝ):ℂ)
  | some (.inl i) => (conj x-conj y)*u i
  | some (.inr i) => (x-y)*conj (u i)

private theorem freq_inj (n : ℕ) : Function.Injective (freq (n:=n)) := by
  rintro (_|(i|i)) (_|(j|j)) h <;> simp only [freq] at h
  all_goals first
    | rfl
    | exact congrArg (fun q : Fin n => some (Sum.inl q)) (gap_injective n (neg_inj.mp h))
    | exact congrArg (fun q : Fin n => some (Sum.inr q)) (gap_injective n h)
    | exfalso; linarith only [h,gap_pos i,gap_pos j]
    | exfalso; linarith only [h,gap_pos i]
    | exfalso; linarith only [h,gap_pos j]

private theorem spectral_row {n : ℕ} (u : Fin n → ℂ) (x y : ℂ) (t : ℝ) :
    ∑ j, mass u x y j*wave (t*freq j) =
       ((lastReading u x t-lastReading u y t:ℝ):ℂ) := by
  have hneg (g : ℝ) : t*(-g)= -t*g := by ring
  have hc : conj (reference u t)=∑ i, conj (u i)*wave (t*gap i) := by
    simp [reference,map_sum,map_mul,conj_wave]
  have hz : wave 0=1 := by simp [wave]
  rw [Fintype.sum_option,Fintype.sum_sum_type]
  simp only [mass,freq,mul_zero,hz,mul_one,hneg,mul_assoc,←Finset.mul_sum,←hc,←reference]
  simp only [lastReading,Complex.ofReal_sub,←Complex.normSq_eq_norm_sq,←Complex.mul_conj,map_add]
  ring

/-- Step size keeps every signed log gap strictly inside the injective
principal arc of the exponential, including the extreme first site. -/
def gridStep (n : ℕ) := 1/(1+Real.log (n+1:ℕ))
private theorem grid_inj (n : ℕ) : Function.Injective (fun i : Index n => wave (gridStep n*freq i)) := by
  have hL := Real.log_natCast_nonneg (n+1)
  have hp : 0 < gridStep n := by dsimp [gridStep]; positivity
  have hh (i : Index n) : |gridStep n*freq i| < 1 := by
    rw [abs_mul,abs_of_pos hp,gridStep,one_div,inv_mul_eq_div,div_lt_one (by positivity)]
    rcases i with _|i; · simp [freq]; linarith
    rcases i with i|i <;> simp only [freq,abs_neg,abs_of_pos (gap_pos i)] <;> linarith only [gap_le i]
  intro i j he
  have hi := abs_lt.mp (hh i)
  have hj := abs_lt.mp (hh j)
  have hπ := Real.pi_gt_three
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x:=((gridStep n*freq i:ℝ):ℂ)*I) (y:=((gridStep n*freq j:ℝ):ℂ)*I)
    (by simpa only [Complex.mul_I_im,Complex.ofReal_re] using (show -Real.pi < gridStep n*freq i by linarith))
    (by simpa only [Complex.mul_I_im,Complex.ofReal_re] using (show gridStep n*freq i ≤ Real.pi by linarith))
    (by simpa only [Complex.mul_I_im,Complex.ofReal_re] using (show -Real.pi < gridStep n*freq j by linarith))
    (by simpa only [Complex.mul_I_im,Complex.ofReal_re] using (show gridStep n*freq j ≤ Real.pi by linarith)) he
  have h := congrArg Complex.im heq
  simp only [Complex.mul_I_im,Complex.ofReal_re] at h
  exact freq_inj n ((mul_left_cancel₀ hp.ne') h)

private theorem finite_vandermonde {ι : Type*} [Fintype ι] (z a : ι → ℂ) (hz : Function.Injective z)
    (h : ∀ k < Fintype.card ι, ∑ i, a i*z i^k=0) : ∀ i, a i=0 := by
  classical
  let e := Fintype.equivFin ι
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f:=z ∘ e.symm) (v:=a ∘ e.symm)
    (hz.comp e.symm.injective) (fun j => by
      simpa only [Function.comp_apply] using
        (Equiv.sum_comp e.symm (fun i => a i*z i^(j:ℕ))).trans (h j j.isLt))
  intro i
  simpa only [Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun hv (e i)

/-- For every nonzero known prefix, 2n+1 fixed consecutive grid readings
determine the last complex coefficient. -/
theorem optimal_grid_identifies_last {n : ℕ} (u : Fin n → ℂ) (hu : u ≠ 0) (x y : ℂ)
    (h : ∀ k < 2*n+1, lastReading u x (k*gridStep n)=lastReading u y (k*gridStep n)) : x=y := by
  have hcard : Fintype.card (Index n)=2*n+1 := by simp [Index] <;> omega
  have hm := finite_vandermonde (fun i : Index n => wave (gridStep n*freq i)) (mass u x y)
    (grid_inj n) (fun k hk => by
      have hs := spectral_row u x y (k*gridStep n)
      simp only [mul_assoc,wave_mul_nat,h k (hcard ▸ hk),sub_self,Complex.ofReal_zero] at hs
      exact hs)
  by_contra hxy
  apply hu
  funext i
  have hz := hm (some (Sum.inr i))
  change (x-y)*conj (u i)=0 at hz
  have he := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hxy)
  simpa using congrArg conj he

private def referenceRe {n : ℕ} (t : ℝ) : (Fin n → ℂ) →ₗ[ℝ] ℝ where
  toFun u := (reference u t).re
  map_add' u v := by simp [reference,add_mul,sum_add_distrib]
  map_smul' k u := by
    simp only [reference,Pi.smul_apply,Complex.real_smul,smul_eq_mul,mul_assoc,
      ←Finset.mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      RingHom.id_apply]

/-- Even with the entire nonzero reference prefix known, every fixed choice
of at most 2n readings confuses two distinct real last coefficients for
some reference. Real and imaginary parts of the reference give 2n degrees
of freedom; one common real projection suffices for an ambiguity. -/
theorem fewer_shifts_confuse_last {n m : ℕ} (hn : 0<n) (hm : m ≤ 2*n) (t : Fin m → ℝ) :
    ∃ (u : Fin n → ℂ) (x y : ℝ), u ≠ 0 ∧ x ≠ y ∧
      ∀ i, lastReading u x (t i)=lastReading u y (t i) := by
  cases m with
  | zero =>
    refine ⟨fun _ => 1,0,1,?_,zero_ne_one,fun i => Fin.elim0 i⟩
    intro h
    simpa using congrFun h ⟨0,hn⟩
  | succ m =>
    have hdim : Fintype.card (Fin m) < Module.finrank ℝ (Fin n → ℂ) := by
      simp only [Module.finrank_pi_fintype,Complex.finrank_real_complex,sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      omega
    obtain ⟨u,hu,hker⟩ := GaloisForLFunctions.HTGeometry.exists_ne_zero_forall_apply_eq_zero_of_finrank_lt
      (fun j : Fin m => referenceRe (t j.succ)-referenceRe (t 0)) hdim
    let w := (reference u (t 0)).re
    have hw (i : Fin (m+1)) : (reference u (t i)).re=w := by
      refine Fin.cases rfl (fun j => ?_) i
      exact sub_eq_zero.mp (hker j)
    refine ⟨u,1-w,-1-w,hu,by linarith,fun i => ?_⟩
    simp only [lastReading,←Complex.normSq_eq_norm_sq,Complex.normSq_apply,
      Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,zero_add,hw]
    ring

end LastCoefficient
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
