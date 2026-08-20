/-
# The sufficiency half of the determinant-completion law, on the spectral side

Correcting the truncation of an `ℓ^p` spectrum by a micro-spectrum block with the prescribed low
moments makes the *plain* determinant of the finite spectrum equal to the order-`p` regularized
determinant times `exp(Q)` -- exactly, at every truncation order.  Since the high moments converge,
the regularized determinants converge, so the plain determinants converge to `exp(Q)·det_p`.

Main results:
* `eval_eq_sum_shift` — a jet with vanishing constant term is its shifted coefficient sum.
* `exists_finiteSpectra_plainDet` — **the sufficiency family**: finite spectra whose plain
  determinants are `exp(Q)` times their regularized ones, with high moments converging.
* `exists_finiteSpectra_tendsto_plainDet` — **the sufficiency half of `(DC)` on the spectral side**:
  the plain determinants converge to `exp(Q)` times the order-`p` regularized determinant.
-/
import GaloisForLFunctions.HTGeometry.VanishingMicroSpectrumFamily
import GaloisForLFunctions.HTGeometry.MultisetSpectrumDeterminant

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem eval_eq_sum_shift {p : ℕ} (hp : 0 < p) {Q : Polynomial ℂ} (hdeg : Q.natDegree ≤ p - 1)
    (hQ0 : Q.coeff 0 = 0) (z : ℂ) :
    Polynomial.eval z Q = ∑ j ∈ Finset.range (p - 1), Q.coeff (j + 1) * z ^ (j + 1) := by
  have hlt : Q.natDegree < p := lt_of_le_of_lt hdeg (by omega)
  rw [Polynomial.eval_eq_sum_range' hlt]
  have hp1 : p = (p - 1) + 1 := by omega
  conv_lhs => rw [hp1]
  rw [Finset.sum_range_succ', hQ0]
  simp

/-- **The sufficiency family.**  For every `ℓ^p` spectrum and every jet of degree below `p` with
vanishing constant term there are finite spectra whose plain determinants are `exp(Q)` times their
order-`p` regularized determinants, with uniformly bounded energy and sup, and with power traces
above the order converging to those of the spectrum. -/
theorem exists_finiteSpectra_plainDet {p : ℕ} (hp : 0 < p) {lam : ℕ → ℂ}
    (hlam : IsSchattenSpectrum p lam) {Bd : ℝ} (hBd : ∀ i, ‖lam i‖ ≤ Bd)
    {Q : Polynomial ℂ} (hdeg : Q.natDegree ≤ p - 1) (hQ0 : Q.coeff 0 = 0) :
    ∃ Sfin : ℕ → Multiset ℂ,
      (∀ n : ℕ, ∀ z : ℂ,
        ‖z‖ * Real.sqrt (matHSNormSq (Matrix.diagonal (multisetIndex (Sfin n)))) < 1 →
          ((Sfin n).map fun μ => 1 - z * μ).prod
            = schattenDet p (multisetIndex (Sfin n)) z * Complex.exp (Polynomial.eval z Q)) ∧
      (∀ n, ((Sfin n).map fun z => ‖z‖ ^ p).sum ≤ (∑' i, ‖lam i‖ ^ p) + 1) ∧
      (∀ n, ∀ z ∈ Sfin n, ‖z‖ ≤ max Bd 1) ∧
      (∀ m, p ≤ m → Tendsto (fun n => schattenTracePower (multisetIndex (Sfin n)) m) atTop
        (nhds (schattenTracePower lam m))) := by
  obtain ⟨Sfin, hlow, henergy, hsup, hhigh⟩ :=
    exists_microSpectrumFamily hp hlam hBd (fun k => -(k : ℂ) * Q.coeff k)
  refine ⟨Sfin, ?_, henergy, hsup, ?_⟩
  · intro n z hz
    have hsum : (∑ j ∈ Finset.range (p - 1),
        z ^ (j + 1) * ((Sfin n).map fun μ => μ ^ (j + 1)).sum / ((j + 1 : ℕ) : ℂ))
        = -∑ j ∈ Finset.range (p - 1), Q.coeff (j + 1) * z ^ (j + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j + 1 ≤ p - 1 := by
        have := Finset.mem_range.mp hj
        omega
      rw [hlow n (j + 1) (by omega) hjle]
      have hne : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
      field_simp
    rw [multiset_prod_one_sub_eq_schattenDet_mul_exp hp (Sfin n) hz, hsum, neg_neg,
      ← eval_eq_sum_shift hp hdeg hQ0]
  · intro m hm
    refine (hhigh m hm).congr fun n => ?_
    rw [multiset_schattenTracePower]

set_option maxHeartbeats 1000000 in
/-- **The sufficiency half of the completion law on the spectral side.**  The plain determinants of
the correcting finite spectra converge to `exp(Q)` times the order-`p` regularized determinant of
the original spectrum, on the disc of the spectral radius. -/
theorem exists_finiteSpectra_tendsto_plainDet {p : ℕ} (hp : 0 < p) {lam : ℕ → ℂ}
    (hlam : IsSchattenSpectrum p lam) {Bd : ℝ} (hBd1 : 1 ≤ Bd) (hBd : ∀ i, ‖lam i‖ ≤ Bd)
    {Q : Polynomial ℂ} (hdeg : Q.natDegree ≤ p - 1) (hQ0 : Q.coeff 0 = 0) :
    ∃ Sfin : ℕ → Multiset ℂ,
      (∀ n : ℕ, ∀ z : ℂ,
        ‖z‖ * Real.sqrt (matHSNormSq (Matrix.diagonal (multisetIndex (Sfin n)))) < 1 →
          ((Sfin n).map fun μ => 1 - z * μ).prod
            = schattenDet p (multisetIndex (Sfin n)) z * Complex.exp (Polynomial.eval z Q)) ∧
      (∀ z : ℂ, ‖z‖ * Bd < 1 →
        Tendsto (fun n => schattenDet p (multisetIndex (Sfin n)) z) atTop
          (nhds (schattenDet p lam z))) := by
  obtain ⟨Sfin, hprod, henergy, hsup, hhigh⟩ :=
    exists_finiteSpectra_plainDet hp hlam hBd hdeg hQ0
  set E : ℝ := ∑' i, ‖lam i‖ ^ p with hE
  have hE0 : 0 ≤ E := tsum_nonneg fun i => pow_nonneg (norm_nonneg _) p
  have hBd0 : (0 : ℝ) ≤ Bd := le_trans zero_le_one hBd1
  have hmax : max Bd 1 = Bd := max_eq_left hBd1
  have hbound : ∀ (n : ℕ) (k : ℕ),
      ‖schattenTracePower (multisetIndex (Sfin n)) (k + p)‖ ≤ (E + 1) * Bd ^ k := by
    intro n k
    rw [multiset_schattenTracePower]
    have hnorm : ‖((Sfin n).map fun z => z ^ (k + p)).sum‖
        ≤ ((Sfin n).map fun z => ‖z‖ ^ (k + p)).sum := by
      refine le_trans (norm_multiset_sum_le _) (le_of_eq ?_)
      rw [Multiset.map_map]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => norm_pow z (k + p))
    have hterm : ∀ z ∈ Sfin n, ‖z‖ ^ (k + p) ≤ Bd ^ k * ‖z‖ ^ p := by
      intro z hz
      have hzle : ‖z‖ ≤ Bd := by
        have := hsup n z hz
        rwa [hmax] at this
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzle k)
        (pow_nonneg (norm_nonneg z) p)
    have hsum : ((Sfin n).map fun z => ‖z‖ ^ (k + p)).sum
        ≤ ((Sfin n).map fun z => Bd ^ k * ‖z‖ ^ p).sum :=
      Multiset.sum_map_le_sum_map _ _ hterm
    have hfac : ((Sfin n).map fun z => Bd ^ k * ‖z‖ ^ p).sum
        = Bd ^ k * ((Sfin n).map fun z => ‖z‖ ^ p).sum := by
      rw [← Multiset.sum_map_mul_left]
    have hen := henergy n
    calc ‖((Sfin n).map fun z => z ^ (k + p)).sum‖
        ≤ ((Sfin n).map fun z => ‖z‖ ^ (k + p)).sum := hnorm
      _ ≤ ((Sfin n).map fun z => Bd ^ k * ‖z‖ ^ p).sum := hsum
      _ = Bd ^ k * ((Sfin n).map fun z => ‖z‖ ^ p).sum := hfac
      _ ≤ Bd ^ k * (E + 1) := mul_le_mul_of_nonneg_left hen (pow_nonneg hBd0 k)
      _ = (E + 1) * Bd ^ k := by ring
  have hboundmu : ∀ k : ℕ, ‖schattenTracePower lam (k + p)‖ ≤ (E + 1) * Bd ^ k := by
    intro k
    calc ‖schattenTracePower lam (k + p)‖ ≤ Bd ^ k * E :=
          norm_schattenTracePower_le (k := k) hp hlam hBd1 hBd
      _ ≤ Bd ^ k * (E + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hBd0 k)
      _ = (E + 1) * Bd ^ k := by ring
  refine ⟨Sfin, hprod, fun z hz => ?_⟩
  exact tendsto_tracePowerDet_of_tendsto (S := E + 1) (B := Bd) hp hBd1 hbound
    (fun k => hhigh (k + p) (Nat.le_add_left p k)) hz

end

end GaloisForLFunctions.HTGeometry
