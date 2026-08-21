import GaloisForLFunctions.RHTower.PairedCauchyLaplaceIdentities

/-!
# The paired transform as a half-line translation-resolvent quadratic form

On the finite real damped-exponential core

```text
E(x) = ∑ⱼ rⱼ e^{-wⱼ x},   y = Im E,   Re wⱼ > 0,
```

the tail resolvent of the right-translation semigroup is

```text
(R_c y)(x) = ∫_0^∞ e^{-c t} y(x + t) dt,
```

which on the core is again a packet, with the resolvent-weighted coefficients `rⱼ/(wⱼ + c)`.  It
satisfies the resolvent differential law `y_c' = c y_c - y` and the exact contact identity

```text
Z_c² + 2 c B_c = 2 ⟨y, R_c y⟩,
```

which converts the Cauchy-atom paired law of `PairedCauchyLaplaceIdentities` into a single
resolvent quadratic value

```text
∑_{j,k} rⱼ r_k P[w ↦ d/(w+c)](wⱼ, w_k) = 8 d ⟨y, R_c y⟩.
```

The last section records the operator algebra of a strict contraction: the geometric resolvent of
`T` and the accretivity of its Cayley transform.  Applied to `T_p = p^{-1/2} S_{log p}` these are
the Euler-prime blocks of the completed translation form.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## The core profile and its tail resolvent -/

/-- The half-line profile `y = Im E` of a node packet. -/
def packetProfile (w : Fin n → ℂ) (r : Fin n → ℝ) (x : ℝ) : ℝ := (nodePacket w r x).im

/-- The tail-resolvent profile `y_c = R_c y`. -/
def resolventProfile (w : Fin n → ℂ) (r : Fin n → ℝ) (c : ℝ) (x : ℝ) : ℝ :=
  (halfLineExpPacket w (resolventCoeff w r c) x).im

/-- The half-line pairing `⟨y, R_c y⟩`. -/
def packetResolventPairing (w : Fin n → ℂ) (r : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), packetProfile w r x * resolventProfile w r c x

theorem resolventCoeff_mul (w : Fin n → ℂ) (r : Fin n → ℝ) (c : ℝ)
    (hc : ∀ j, w j + (c : ℂ) ≠ 0) (j : Fin n) :
    resolventCoeff w r c j * (w j + (c : ℂ)) = (r j : ℂ) :=
  div_mul_cancel₀ _ (hc j)

/-! ## Equation `(4)`: the resolvent of the core is a packet -/

theorem integrableOn_exp_neg_atom {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-α * (t : ℂ))) (Ioi 0) := by
  simpa using integrableOn_exp_mul_complex_Ioi (a := -α) (by simpa using hα) 0

theorem integral_exp_neg_atom {α : ℂ} (hα : 0 < α.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-α * (t : ℂ)) = 1 / α := by
  have h := integral_exp_mul_complex_Ioi (a := -α) (by simpa using hα) 0
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0] at hα
    simp at hα
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h]
  field_simp

/-- **Equation `(4)`.**  On the core the tail resolvent is again a packet, with coefficients
`rⱼ/(wⱼ + c)`. -/
theorem integral_exp_neg_mul_packetProfile {w : Fin n → ℂ} (r : Fin n → ℝ) {c : ℝ}
    (hwc : ∀ j, 0 < (w j + (c : ℂ)).re) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(c * t)) * packetProfile w r (x + t)
      = resolventProfile w r c x := by
  classical
  have hne : ∀ j, w j + (c : ℂ) ≠ 0 := by
    intro j h
    have := hwc j
    rw [h] at this
    simp at this
  have hE : ∀ (t : ℝ) (j : Fin n), (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
        * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))
      = ((Real.exp (-(c * t)) : ℝ) : ℂ)
        * ((r j : ℂ) * Complex.exp (-(w j) * ((x + t : ℝ) : ℂ))) := by
    intro t j
    rw [Complex.ofReal_exp]
    rw [show ((r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
          * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ)))
        = (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ) + -(w j + (c : ℂ)) * (t : ℂ)) from by
      rw [Complex.exp_add]; ring]
    rw [show (Complex.exp ((-(c * t) : ℝ) : ℂ)
          * ((r j : ℂ) * Complex.exp (-(w j) * ((x + t : ℝ) : ℂ))))
        = (r j : ℂ) * Complex.exp (((-(c * t) : ℝ) : ℂ) + -(w j) * ((x + t : ℝ) : ℂ)) from by
      rw [Complex.exp_add]; ring]
    congr 2
    push_cast
    ring
  have hpoint : ∀ t : ℝ, (Real.exp (-(c * t)) : ℝ) * packetProfile w r (x + t)
      = (∑ j, (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
          * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))).im := by
    intro t
    rw [Finset.sum_congr rfl (fun j _ => hE t j), ← Finset.mul_sum, Complex.im_ofReal_mul]
    rfl
  have hintj : ∀ j : Fin n, IntegrableOn
      (fun t : ℝ => (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
        * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))) (Ioi 0) :=
    fun j => (integrableOn_exp_neg_atom (hwc j)).const_mul _
  have hsum : IntegrableOn
      (fun t : ℝ => ∑ j, (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
        * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))) (Ioi 0) :=
    integrable_finsetSum _ fun j _ => hintj j
  have him : (∫ t in Ioi (0 : ℝ), (∑ j, (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
        * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))).im)
      = (∫ t in Ioi (0 : ℝ), ∑ j, (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
        * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))).im := integral_im hsum
  have hcast : (∫ t in Ioi (0 : ℝ), Real.exp (-(c * t)) * packetProfile w r (x + t))
      = (∫ t in Ioi (0 : ℝ), ∑ j, (r j : ℂ) * Complex.exp (-(w j) * (x : ℂ))
          * Complex.exp (-(w j + (c : ℂ)) * (t : ℂ))).im := by
    rw [← him]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hcast, integral_finsetSum _ fun j _ => hintj j]
  unfold resolventProfile halfLineExpPacket resolventCoeff
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_exp_neg_atom (hwc j)]
  field_simp

/-! ## Equation `(5)`: the resolvent differential law -/

/-- **Equation `(5)`.**  `y_c' = c y_c - y`. -/
theorem hasDerivAt_resolventProfile {w : Fin n → ℂ} (r : Fin n → ℝ) {c : ℝ}
    (hc : ∀ j, w j + (c : ℂ) ≠ 0) (x : ℝ) :
    HasDerivAt (resolventProfile w r c)
      (c * resolventProfile w r c x - packetProfile w r x) x := by
  classical
  have hderiv : HasDerivAt (fun x : ℝ => halfLineExpPacket w (resolventCoeff w r c) x)
      (∑ j, resolventCoeff w r c j * (-(w j)) * Complex.exp (-(w j) * (x : ℂ))) x := by
    unfold halfLineExpPacket
    refine HasDerivAt.fun_sum fun j _ => ?_
    have hb : HasDerivAt (fun x : ℝ => Complex.exp (-(w j) * (x : ℂ)))
        (Complex.exp (-(w j) * (x : ℂ)) * (-(w j))) x := by
      have h1 : HasDerivAt (fun x : ℝ => (-(w j)) * (x : ℂ)) (-(w j)) x := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(w j)))
      simpa using h1.cexp
    have hcm := hb.const_mul (resolventCoeff w r c j)
    have hre : resolventCoeff w r c j * (Complex.exp (-(w j) * (x : ℂ)) * (-(w j)))
        = resolventCoeff w r c j * (-(w j)) * Complex.exp (-(w j) * (x : ℂ)) := by ring
    rwa [hre] at hcm
  have hval : (∑ j, resolventCoeff w r c j * (-(w j)) * Complex.exp (-(w j) * (x : ℂ)))
      = (c : ℂ) * halfLineExpPacket w (resolventCoeff w r c) x - nodePacket w r x := by
    simp only [nodePacket, halfLineExpPacket, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := resolventCoeff_mul w r c hc j
    have hstep : resolventCoeff w r c j * (-(w j))
        = (c : ℂ) * resolventCoeff w r c j - (r j : ℂ) := by
      rw [← hj]; ring
    rw [hstep]
    ring
  rw [hval] at hderiv
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hderiv
  have hval2 : Complex.imCLM ((c : ℂ) * halfLineExpPacket w (resolventCoeff w r c) x
      - nodePacket w r x) = c * resolventProfile w r c x - packetProfile w r x := by
    simp [resolventProfile, packetProfile, Complex.sub_im]
  rw [hval2] at him
  exact him

/-! ## Equation `(6)`: the contact identity, and `(7)`-`(9)` in operator form -/

theorem bilSum_resolvent_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {c : ℝ}
    (hc : ∀ j, w j + (c : ℂ) ≠ 0) :
    2 * (∑ j, ∑ k, (r j : ℂ) * resolventCoeff w r c k / (w j + w k))
      = (∑ j, resolventCoeff w r c j) ^ 2
        + 2 * (c : ℂ) * ∑ j, ∑ k,
            resolventCoeff w r c j * resolventCoeff w r c k / (w j + w k) := by
  classical
  set s : Fin n → ℂ := resolventCoeff w r c with hsdef
  have hwjk : ∀ j k, w j + w k ≠ 0 := fun j k => add_ne_zero_of_re_pos (hw j) (hw k)
  have hkey : ∀ j k, (r j : ℂ) * s k / (w j + w k) + s j * (r k : ℂ) / (w j + w k)
      = s j * s k + 2 * (c : ℂ) * (s j * s k / (w j + w k)) := by
    intro j k
    have hj : s j * (w j + (c : ℂ)) = (r j : ℂ) := resolventCoeff_mul w r c hc j
    have hk : s k * (w k + (c : ℂ)) = (r k : ℂ) := resolventCoeff_mul w r c hc k
    have hjk := hwjk j k
    rw [← hj, ← hk]
    field_simp
    ring
  have hL : (∑ j, ∑ k, ((r j : ℂ) * s k / (w j + w k) + s j * (r k : ℂ) / (w j + w k)))
      = ∑ j, ∑ k, (s j * s k + 2 * (c : ℂ) * (s j * s k / (w j + w k))) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hkey j k
  rw [sum_sum_add, sum_sum_add, sum_sum_mul_factor, sum_sum_const_mul,
    bilSum_swap w s (fun k => (r k : ℂ))] at hL
  rw [← sq] at hL
  linear_combination hL

theorem hermSum_resolvent_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {c : ℝ}
    (hc : ∀ j, w j + (c : ℂ) ≠ 0) :
    2 * (∑ j, ∑ k, (starRingEnd ℂ) ((r j : ℂ)) * resolventCoeff w r c k
            / ((starRingEnd ℂ) (w j) + w k)).re
      = ‖∑ j, resolventCoeff w r c j‖ ^ 2
        + 2 * c * (∑ j, ∑ k, (starRingEnd ℂ) (resolventCoeff w r c j) * resolventCoeff w r c k
            / ((starRingEnd ℂ) (w j) + w k)).re := by
  classical
  set s : Fin n → ℂ := resolventCoeff w r c with hsdef
  have hwjk : ∀ j k, (starRingEnd ℂ) (w j) + w k ≠ 0 := fun j k =>
    add_ne_zero_of_re_pos (by simpa using hw j) (hw k)
  have hconj : ∀ j, (starRingEnd ℂ) (s j) * ((starRingEnd ℂ) (w j) + (c : ℂ)) = (r j : ℂ) := by
    intro j
    have hj : s j * (w j + (c : ℂ)) = (r j : ℂ) := resolventCoeff_mul w r c hc j
    have := congrArg (starRingEnd ℂ) hj
    simpa [map_mul, map_add, Complex.conj_ofReal] using this
  have hkey : ∀ j k, (starRingEnd ℂ) ((r j : ℂ)) * s k / ((starRingEnd ℂ) (w j) + w k)
        + (starRingEnd ℂ) (s j) * (r k : ℂ) / ((starRingEnd ℂ) (w j) + w k)
      = (starRingEnd ℂ) (s j) * s k
        + 2 * (c : ℂ) * ((starRingEnd ℂ) (s j) * s k / ((starRingEnd ℂ) (w j) + w k)) := by
    intro j k
    have hj := hconj j
    have hk : s k * (w k + (c : ℂ)) = (r k : ℂ) := resolventCoeff_mul w r c hc k
    have hjk := hwjk j k
    rw [Complex.conj_ofReal, ← hj, ← hk]
    field_simp
    ring
  have hL : (∑ j, ∑ k, ((starRingEnd ℂ) ((r j : ℂ)) * s k / ((starRingEnd ℂ) (w j) + w k)
        + (starRingEnd ℂ) (s j) * (r k : ℂ) / ((starRingEnd ℂ) (w j) + w k)))
      = ∑ j, ∑ k, ((starRingEnd ℂ) (s j) * s k
          + 2 * (c : ℂ) * ((starRingEnd ℂ) (s j) * s k / ((starRingEnd ℂ) (w j) + w k))) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hkey j k
  rw [sum_sum_add, sum_sum_add, sum_sum_mul_factor, sum_sum_const_mul] at hL
  have hswap : (∑ j, ∑ k, (starRingEnd ℂ) (s j) * (r k : ℂ) / ((starRingEnd ℂ) (w j) + w k))
      = (starRingEnd ℂ) (∑ j, ∑ k,
          (starRingEnd ℂ) ((r j : ℂ)) * s k / ((starRingEnd ℂ) (w j) + w k)) := by
    rw [map_sum]
    have hinner : ∀ j, (starRingEnd ℂ) (∑ k,
          (starRingEnd ℂ) ((r j : ℂ)) * s k / ((starRingEnd ℂ) (w j) + w k))
        = ∑ k, (r j : ℂ) * (starRingEnd ℂ) (s k) / (w j + (starRingEnd ℂ) (w k)) := by
      intro j
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_div₀, map_mul, map_add, Complex.conj_conj]
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    exact (hermSum_swap w (fun j => (r j : ℂ)) s).symm
  rw [hswap] at hL
  have hnorm : ((∑ j, (starRingEnd ℂ) (s j)) * ∑ k, s k).re = ‖∑ j, s j‖ ^ 2 := by
    rw [← map_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hc2 : (2 * (c : ℂ) * ∑ j, ∑ k,
      (starRingEnd ℂ) (s j) * s k / ((starRingEnd ℂ) (w j) + w k)).re
      = 2 * c * (∑ j, ∑ k,
        (starRingEnd ℂ) (s j) * s k / ((starRingEnd ℂ) (w j) + w k)).re := by
    rw [show (2 : ℂ) * (c : ℂ) = ((2 * c : ℝ) : ℂ) from by push_cast; ring, ofReal_mul_re]
  have hre := congrArg Complex.re hL
  rw [Complex.add_re, Complex.conj_re, Complex.add_re, hnorm, hc2] at hre
  linarith [hre]

/-- **Equation `(6)`.**  The exact contact identity `Z_c² + 2 c B_c = 2 ⟨y, R_c y⟩`. -/
theorem resolvent_contact_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {c : ℝ}
    (hc : ∀ j, w j + (c : ℂ) ≠ 0) :
    (resolventValueIm w r c) ^ 2 + 2 * c * resolventEnergy w r c
      = 2 * packetResolventPairing w r c := by
  classical
  set s : Fin n → ℂ := resolventCoeff w r c with hsdef
  set S : ℂ := ∑ j, s j with hS
  set Brs : ℂ := ∑ j, ∑ k, (r j : ℂ) * s k / (w j + w k) with hBrs
  set Bss : ℂ := ∑ j, ∑ k, s j * s k / (w j + w k) with hBss
  set Hrs : ℂ := ∑ j, ∑ k,
    (starRingEnd ℂ) ((r j : ℂ)) * s k / ((starRingEnd ℂ) (w j) + w k) with hHrs
  set Hss : ℂ := ∑ j, ∑ k,
    (starRingEnd ℂ) (s j) * s k / ((starRingEnd ℂ) (w j) + w k) with hHss
  set P : ℝ := ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w (fun j => (r j : ℂ)) x).im
    * (halfLineExpPacket w s x).im with hP
  set E : ℝ := ∫ x in Ioi (0 : ℝ), (halfLineExpPacket w s x).im ^ 2 with hE
  have hcross : 2 * P = Hrs.re - Brs.re :=
    integral_im_mul_im_expPacket (w := w) (fun j => (r j : ℂ)) s hw
  have hsq : 2 * E = Hss.re - Bss.re := integral_im_sq_expPacket (w := w) (c := s) hw
  have hherm : 2 * Hrs.re = ‖S‖ ^ 2 + 2 * c * Hss.re := hermSum_resolvent_law hw r hc
  have hbil : 2 * Brs = S ^ 2 + 2 * (c : ℂ) * Bss := bilSum_resolvent_law hw r hc
  have hbilre : 2 * Brs.re = (S ^ 2).re + 2 * c * Bss.re := by
    have h := congrArg Complex.re hbil
    rw [show (2 : ℂ) * Brs = ((2 : ℝ) : ℂ) * Brs from by norm_num,
      show (2 : ℂ) * (c : ℂ) * Bss = ((2 * c : ℝ) : ℂ) * Bss from by push_cast; ring,
      Complex.add_re, ofReal_mul_re, ofReal_mul_re] at h
    exact h
  have hZ : ‖S‖ ^ 2 - (S ^ 2).re = 2 * (resolventValueIm w r c) ^ 2 := by
    rw [normSq_sub_re_sq]
    rfl
  have hPeq : packetResolventPairing w r c = P := rfl
  have hEeq : resolventEnergy w r c = E := rfl
  rw [hPeq, hEeq]
  linear_combination (-1 : ℝ) * hcross + c * hsq + (-1/2 : ℝ) * hherm + (1/2 : ℝ) * hbilre
    + (-1/2 : ℝ) * hZ

/-- **Equation `(7)`.**  A real Cauchy atom is one resolvent quadratic value. -/
theorem paired_resolvent_law {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) (d : ℝ)
    {c : ℝ} (hc : ∀ j, w j + (c : ℂ) ≠ 0) :
    pairedQuadratic w r (fun z => (d : ℂ) / (z + (c : ℂ)))
      = 8 * d * packetResolventPairing w r c := by
  rw [paired_cauchyAtom_law hw r d c hc]
  have hcontact := resolvent_contact_law hw r hc
  linear_combination (4 * d) * hcontact

/-- **Equation `(9)`, translation form.**  The lag autocorrelation is the translation pairing
`⟨y, S_τ y⟩`. -/
theorem packetAutocorrelation_eq_translation_pairing (w : Fin n → ℂ) (r : Fin n → ℝ) (tau : ℝ) :
    packetAutocorrelation w r tau
      = ∫ x in Ioi (0 : ℝ), packetProfile w r x * packetProfile w r (x + tau) := by
  unfold packetAutocorrelation packetProfile
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (nodePacket w r x).im * (halfLineExpPacket w (lagCoeff w r tau) x).im
    = (nodePacket w r x).im * (nodePacket w r (x + tau)).im
  rw [expPacket_lagCoeff]

/-! ## Euler-prime blocks: the geometric resolvent and its Cayley part

A prime block of the critical Euler translation form is `∑_{k≥1} log p · p^{-k/2} S_{k log p}`,
that is `log p` times the geometric series of the strict contraction `T_p = p^{-1/2} S_{log p}`.
The two statements the card uses are the resolvent form of that series and the accretivity of the
Cayley transform of a contraction. -/

section GeometricResolvent

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- **Equation `(16)`.**  The strictly contractive geometric block is a resolvent. -/
theorem tsum_pow_succ_eq_mul_inverse (T : R) (h : ‖T‖ < 1) :
    ∑' k : ℕ, T ^ (k + 1) = T * Ring.inverse (1 - T) := by
  rw [← geom_series_mul_shift T h, geom_series_eq_inverse T h]

theorem one_sub_mul_inverse (T : R) (h : ‖T‖ < 1) :
    (1 - T) * Ring.inverse (1 - T) = 1 := by
  rw [← geom_series_eq_inverse T h]
  exact mul_neg_geom_series T h

/-- **Equation `(17)`.**  The geometric resolvent is the Cayley transform minus one contact
subtraction. -/
theorem one_add_mul_inverse_eq (T : R) (h : ‖T‖ < 1) :
    (1 + T) * Ring.inverse (1 - T) = 1 + 2 * (T * Ring.inverse (1 - T)) := by
  have h1 := one_sub_mul_inverse T h
  have hsplit : (1 + T) * Ring.inverse (1 - T)
      = (1 - T) * Ring.inverse (1 - T) + 2 * (T * Ring.inverse (1 - T)) := by
    noncomm_ring
  rw [hsplit, h1]

end GeometricResolvent

section Cayley

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Cayley form of a contraction is accretive.**  Its real part is the norm defect. -/
theorem re_inner_cayley_eq (T : H →L[ℂ] H) (v : H) :
    (inner ℂ ((1 + T) v) ((1 - T) v) : ℂ).re = ‖v‖ ^ 2 - ‖T v‖ ^ 2 := by
  have hexp : (inner ℂ ((1 + T) v) ((1 - T) v) : ℂ)
      = (inner ℂ v v : ℂ) - (inner ℂ v (T v) : ℂ) + (inner ℂ (T v) v : ℂ)
        - (inner ℂ (T v) (T v) : ℂ) := by
    simp only [add_apply, sub_apply, one_apply_eq_self, inner_add_left, inner_sub_right]
    ring
  have hconj : (inner ℂ v (T v) : ℂ) = (starRingEnd ℂ) (inner ℂ (T v) v : ℂ) :=
    (inner_conj_symm (𝕜 := ℂ) v (T v)).symm
  rw [hexp, hconj]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The Cayley quadratic form of a contraction is accretive. -/
theorem re_inner_cayley_nonneg {T : H →L[ℂ] H} (hT : ‖T‖ ≤ 1) (v : H) :
    0 ≤ (inner ℂ ((1 + T) v) ((1 - T) v) : ℂ).re := by
  rw [re_inner_cayley_eq]
  have h1 : ‖T v‖ ≤ ‖v‖ := by
    calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ 1 * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right hT (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have := sq_le_sq' (by linarith [norm_nonneg (T v), norm_nonneg v] : -‖v‖ ≤ ‖T v‖) h1
  linarith

/-- A real multiple of a contraction with factor below one is a strict contraction. -/
theorem norm_real_smul_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) {T : H →L[ℂ] H}
    (hT : ‖T‖ ≤ 1) : ‖((t : ℂ)) • T‖ < 1 := by
  have hnorm : ‖((t : ℂ)) • T‖ = t * ‖T‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [hnorm]
  calc t * ‖T‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hT ht0
    _ = t := mul_one t
    _ < 1 := ht

/-- **The Euler-prime block is a strict contraction.**  `T_p = p^{-1/2} S_{log p}` has norm below
one for every `p > 1` and every contraction `S`. -/
theorem norm_eulerPrimeBlock_lt_one {p : ℝ} (hp : 1 < p) {T : H →L[ℂ] H} (hT : ‖T‖ ≤ 1) :
    ‖(((Real.sqrt p)⁻¹ : ℝ) : ℂ) • T‖ < 1 := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hsq : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt zero_le_one hp
  refine norm_real_smul_lt_one (by positivity) ?_ hT
  rw [inv_lt_one_iff₀]
  exact Or.inr hsq

end Cayley

end

end RHTower


