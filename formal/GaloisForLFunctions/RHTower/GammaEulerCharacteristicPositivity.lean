import Mathlib
import GaloisForLFunctions.RHTower.MobiusGammaEulerDifferenceTailParity

/-!
# One Euler channel preserves the Gamma correlation sign

A single normalized Euler factor acts on the Gamma height characteristic `φ_r(u) = sech(u/2)^r` by the
Gamma-Euler central difference, and that action is everywhere strictly positive
(`gammaEulerCentralDifference_cosh_rpow_pos`).  Equivalently one Euler channel preserves the
correlation sign — the monotone Gamma contraction fails only after the *second* channel, which is the
tail-parity obstruction.

The core is the symmetric-sum monotonicity `euler_ratio_core`: for `0 < s < c` and `r > 0` the even
map `T ↦ (c+sT)^{-r} + (c-sT)^{-r}` is strictly increasing in `|T|` on `[0,1)`, so its value at
`T = tanh(u/2)` stays strictly below the endpoint `(c+s)^{-r} + (c-s)^{-r} = 2 cosh(rh/2)`.  Writing
`cosh((u±h)/2) = cosh(u/2)(cosh(h/2) ± sinh(h/2) tanh(u/2))` factors the central difference into
`cosh(u/2)^{-r}` times that strictly positive gap.
-/

open Real Set


namespace RHTower

theorem euler_ratio_core {c s r : ℝ} (hs : 0 < s) (hsc : 0 < c - s) (hr : 0 < r)
    {T : ℝ} (hT : |T| < 1) :
    (c + s * T) ^ (-r) + (c - s * T) ^ (-r) < (c + s) ^ (-r) + (c - s) ^ (-r) := by
  have hc : 0 < c := by linarith
  set f : ℝ → ℝ := fun t => (c + s * t) ^ (-r) + (c - s * t) ^ (-r) with hf
  have hbaseP : ∀ t ∈ Icc (0:ℝ) 1, 0 < c + s * t := fun t ht => by
    rw [mem_Icc] at ht; nlinarith [ht.1, hs]
  have hbaseM : ∀ t ∈ Icc (0:ℝ) 1, 0 < c - s * t := fun t ht => by
    rw [mem_Icc] at ht; nlinarith [ht.2, hs, hsc]
  have hcont : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
        (fun t ht => Or.inl (hbaseP t ht).ne')
    · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).rpow_const
        (fun t ht => Or.inl (hbaseM t ht).ne')
  have hderiv : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f
      (r * s * ((c - s * t) ^ (-r - 1) - (c + s * t) ^ (-r - 1))) t := by
    intro t ht
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hp := hbaseP t htI
    have hm := hbaseM t htI
    have hl1 : HasDerivAt (fun t => c + s * t) s t := by
      simpa using (((hasDerivAt_id t).const_mul s).const_add c)
    have hl2 : HasDerivAt (fun t => c - s * t) (-s) t := by
      simpa using (((hasDerivAt_id t).const_mul s).const_sub c)
    have hd1 := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl hp.ne')).comp t hl1
    have hd2 := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl hm.ne')).comp t hl2
    have hsum := hd1.add hd2
    convert hsum using 1
    ring
  have hmono : StrictMonoOn f (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
    intro t ht
    rw [interior_Icc, mem_Ioo] at ht
    rw [(hderiv t ⟨ht.1, ht.2⟩).deriv]
    have hlt : (c + s * t) ^ (-r - 1) < (c - s * t) ^ (-r - 1) :=
      rpow_lt_rpow_of_neg (hbaseM t ⟨ht.1.le, ht.2.le⟩) (by nlinarith [ht.1, hs]) (by linarith)
    nlinarith [hlt, mul_pos hr hs]
  have heven : ∀ t, f (-t) = f t := fun t => by
    simp only [hf]
    rw [show c + s * (-t) = c - s * t by ring, show c - s * (-t) = c + s * t by ring, add_comm]
  have hTeq : f T = f |T| := by
    rcases abs_choice T with h | h
    · rw [h]
    · rw [h]; exact (heven T).symm
  have h1 : (c + s) ^ (-r) + (c - s) ^ (-r) = f 1 := by simp [hf]
  rw [(by simp [hf] : (c + s * T) ^ (-r) + (c - s * T) ^ (-r) = f T), hTeq, h1]
  exact hmono ⟨abs_nonneg T, hT.le⟩ ⟨zero_le_one, le_refl 1⟩ hT

theorem gammaEulerCentralDifference_cosh_rpow_pos {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (u : ℝ) :
    0 < gammaEulerCentralDifference r h (fun u => (Real.cosh (u / 2)) ^ (-r)) u := by
  set c := Real.cosh (h / 2) with hcdef
  set s := Real.sinh (h / 2) with hsdef
  set T := Real.tanh (u / 2) with hTdef
  have hcu : 0 < Real.cosh (u / 2) := Real.cosh_pos (u / 2)
  have hs : 0 < s := by
    rw [hsdef, Real.sinh_eq]
    have : Real.exp (-(h / 2)) < Real.exp (h / 2) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hcs : c - s = Real.exp (-(h / 2)) := by rw [hcdef, hsdef, Real.cosh_sub_sinh]
  have hsc : 0 < c - s := by rw [hcs]; exact Real.exp_pos _
  have hcps : c + s = Real.exp (h / 2) := Real.cosh_add_sinh _
  have hsinh : Real.sinh (u / 2) = T * Real.cosh (u / 2) := by
    rw [hTdef, Real.tanh_eq_sinh_div_cosh]; field_simp
  have hfacP : Real.cosh ((u + h) / 2) = Real.cosh (u / 2) * (c + s * T) := by
    rw [show (u + h) / 2 = u / 2 + h / 2 by ring, Real.cosh_add, hsinh, hcdef, hsdef]; ring
  have hfacM : Real.cosh ((u - h) / 2) = Real.cosh (u / 2) * (c - s * T) := by
    rw [show (u - h) / 2 = u / 2 - h / 2 by ring, Real.cosh_sub, hsinh, hcdef, hsdef]; ring
  have hsT : |s * T| < s := by
    rw [abs_mul, abs_of_pos hs]
    calc s * |T| < s * 1 := mul_lt_mul_of_pos_left (abs_tanh_lt_one _) hs
      _ = s := mul_one s
  have hposP : 0 < c + s * T := by have := (abs_lt.mp hsT).1; linarith [hsc]
  have hposM : 0 < c - s * T := by have := (abs_lt.mp hsT).2; linarith [hsc]
  have hendpt : 2 * Real.cosh (r * h / 2) = (c + s) ^ (-r) + (c - s) ^ (-r) := by
    rw [hcps, hcs, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.cosh_eq]
    ring_nf
  show 0 < 2 * Real.cosh (r * h / 2) * (Real.cosh (u / 2)) ^ (-r)
    - (Real.cosh ((u + h) / 2)) ^ (-r) - (Real.cosh ((u - h) / 2)) ^ (-r)
  rw [hfacP, hfacM, Real.mul_rpow hcu.le hposP.le, Real.mul_rpow hcu.le hposM.le, hendpt]
  have hcore := euler_ratio_core hs hsc hr (T := T) (abs_tanh_lt_one _)
  have hcru : 0 < (Real.cosh (u / 2)) ^ (-r) := Real.rpow_pos_of_pos hcu _
  nlinarith [hcore, hcru]

end RHTower
