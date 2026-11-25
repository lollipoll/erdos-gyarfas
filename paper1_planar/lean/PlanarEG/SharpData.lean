import Std

/-! Exact O(log n)-depth balanced-tree tables, symmetry generators, & BFS parent certificates for `G168`, `C24`, `G7`, `C60`, `TD60`, and `D20`.
Generated from `cert/witnesses/sharp_witnesses.json`. -/

namespace PlanarEG.SharpData

def c24Nbrs (u : Fin 24) : Fin 24 × Fin 24 × Fin 24 :=
  if u.val < 12 then
    if u.val < 6 then
      if u.val < 3 then
        if u.val < 1 then
          (1, 5, 6)
        else
          if u.val < 2 then
            (0, 2, 7)
          else
            (1, 3, 8)
      else
        if u.val < 4 then
          (2, 4, 9)
        else
          if u.val < 5 then
            (3, 5, 10)
          else
            (0, 4, 11)
    else
      if u.val < 9 then
        if u.val < 7 then
          (0, 12, 17)
        else
          if u.val < 8 then
            (1, 12, 13)
          else
            (2, 13, 14)
      else
        if u.val < 10 then
          (3, 14, 15)
        else
          if u.val < 11 then
            (4, 15, 16)
          else
            (5, 16, 17)
  else
    if u.val < 18 then
      if u.val < 15 then
        if u.val < 13 then
          (6, 7, 18)
        else
          if u.val < 14 then
            (7, 8, 19)
          else
            (8, 9, 20)
      else
        if u.val < 16 then
          (9, 10, 21)
        else
          if u.val < 17 then
            (10, 11, 22)
          else
            (6, 11, 23)
    else
      if u.val < 21 then
        if u.val < 19 then
          (12, 19, 23)
        else
          if u.val < 20 then
            (13, 18, 20)
          else
            (14, 19, 21)
      else
        if u.val < 22 then
          (15, 20, 22)
        else
          if u.val < 23 then
            (16, 21, 23)
          else
            (17, 18, 22)

def c24Port (u v : Fin 24) : Nat :=
  if u.val < 12 then
    if u.val < 6 then
      if u.val < 3 then
        if u.val < 1 then
          if v.val == 1 then 4 else if v.val == 5 then 6 else if v.val == 6 then 5 else 0
        else
          if u.val < 2 then
            if v.val == 0 then 6 else if v.val == 2 then 4 else if v.val == 7 then 5 else 0
          else
            if v.val == 1 then 6 else if v.val == 3 then 4 else if v.val == 8 then 5 else 0
      else
        if u.val < 4 then
          if v.val == 2 then 6 else if v.val == 4 then 4 else if v.val == 9 then 5 else 0
        else
          if u.val < 5 then
            if v.val == 3 then 6 else if v.val == 5 then 4 else if v.val == 10 then 5 else 0
          else
            if v.val == 0 then 4 else if v.val == 4 then 6 else if v.val == 11 then 5 else 0
    else
      if u.val < 9 then
        if u.val < 7 then
          if v.val == 0 then 5 else if v.val == 12 then 6 else if v.val == 17 then 4 else 0
        else
          if u.val < 8 then
            if v.val == 1 then 5 else if v.val == 12 then 4 else if v.val == 13 then 6 else 0
          else
            if v.val == 2 then 5 else if v.val == 13 then 4 else if v.val == 14 then 6 else 0
      else
        if u.val < 10 then
          if v.val == 3 then 5 else if v.val == 14 then 4 else if v.val == 15 then 6 else 0
        else
          if u.val < 11 then
            if v.val == 4 then 5 else if v.val == 15 then 4 else if v.val == 16 then 6 else 0
          else
            if v.val == 5 then 5 else if v.val == 16 then 4 else if v.val == 17 then 6 else 0
  else
    if u.val < 18 then
      if u.val < 15 then
        if u.val < 13 then
          if v.val == 6 then 4 else if v.val == 7 then 5 else if v.val == 18 then 6 else 0
        else
          if u.val < 14 then
            if v.val == 7 then 4 else if v.val == 8 then 5 else if v.val == 19 then 6 else 0
          else
            if v.val == 8 then 4 else if v.val == 9 then 5 else if v.val == 20 then 6 else 0
      else
        if u.val < 16 then
          if v.val == 9 then 4 else if v.val == 10 then 5 else if v.val == 21 then 6 else 0
        else
          if u.val < 17 then
            if v.val == 10 then 4 else if v.val == 11 then 5 else if v.val == 22 then 6 else 0
          else
            if v.val == 6 then 5 else if v.val == 11 then 4 else if v.val == 23 then 6 else 0
    else
      if u.val < 21 then
        if u.val < 19 then
          if v.val == 12 then 5 else if v.val == 19 then 6 else if v.val == 23 then 4 else 0
        else
          if u.val < 20 then
            if v.val == 13 then 5 else if v.val == 18 then 4 else if v.val == 20 then 6 else 0
          else
            if v.val == 14 then 5 else if v.val == 19 then 4 else if v.val == 21 then 6 else 0
      else
        if u.val < 22 then
          if v.val == 15 then 5 else if v.val == 20 then 4 else if v.val == 22 then 6 else 0
        else
          if u.val < 23 then
            if v.val == 16 then 5 else if v.val == 21 then 4 else if v.val == 23 then 6 else 0
          else
            if v.val == 17 then 5 else if v.val == 18 then 6 else if v.val == 22 then 4 else 0

def c24Parent0 (v : Fin 24) : Fin 24 → Fin 24 :=
  if v.val < 12 then
    if v.val < 6 then
      if v.val < 3 then
        if v.val < 1 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
        else
          if v.val < 2 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 2 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 13 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 9 | 4 => 5 | _ => 11) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 13 | 3 => 14 | 4 => 16 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 20 | 4 => 23 | _ => 18))
      else
        if v.val < 4 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 10 | _ => 11) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 14 | 4 => 15 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 23 | _ => 18))
        else
          if v.val < 5 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | _ => 11) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 15 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 1) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
    else
      if v.val < 9 then
        if v.val < 7 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 23) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
        else
          if v.val < 8 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 17 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 18 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 1 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 9 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 23 | _ => 18))
      else
        if v.val < 10 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 23 | _ => 18))
        else
          if v.val < 11 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 1)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
  else
    if v.val < 18 then
      if v.val < 15 then
        if v.val < 13 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 17 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
        else
          if v.val < 14 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 1 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 18 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 1 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 23 | _ => 18))
      else
        if v.val < 16 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 1 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 23 | _ => 18))
        else
          if v.val < 17 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 1 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 1) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
    else
      if v.val < 21 then
        if v.val < 19 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 20 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 1 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 1 | 3 => 15 | 4 => 23 | _ => 18))
      else
        if v.val < 22 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 1 | 4 => 23 | _ => 18))
        else
          if v.val < 23 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 1 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 1))

def c24Parent1 (v : Fin 24) : Fin 24 → Fin 24 :=
  if v.val < 12 then
    if v.val < 6 then
      if v.val < 3 then
        if v.val < 1 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 23) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
        else
          if v.val < 2 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 5 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 2 | 1 => 13 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 4 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 13 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 20 | 4 => 16 | _ => 18))
      else
        if v.val < 4 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 14 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 18))
        else
          if v.val < 5 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 16 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 1) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 16)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 23) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
    else
      if v.val < 9 then
        if v.val < 7 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
        else
          if v.val < 8 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 18 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 9 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 18))
      else
        if v.val < 10 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 18))
        else
          if v.val < 11 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 1)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 23) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
  else
    if v.val < 18 then
      if v.val < 15 then
        if v.val < 13 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 14 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 1 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 18 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 1 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 18))
      else
        if v.val < 16 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 1 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 18))
        else
          if v.val < 17 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 1 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 1) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
    else
      if v.val < 21 then
        if v.val < 19 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 20 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 1 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 1 | 3 => 15 | 4 => 16 | _ => 18))
      else
        if v.val < 22 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 1 | 4 => 16 | _ => 18))
        else
          if v.val < 23 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 1 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 1))

def c24Parent2 (v : Fin 24) : Fin 24 → Fin 24 :=
  if v.val < 12 then
    if v.val < 6 then
      if v.val < 3 then
        if v.val < 1 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 17 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
        else
          if v.val < 2 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 5 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 0 | 1 => 13 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 2 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 4 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 13 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 19 | 3 => 20 | 4 => 16 | _ => 17))
      else
        if v.val < 4 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 14 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 5 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 16 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 1) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
    else
      if v.val < 9 then
        if v.val < 7 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 8 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 23 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 9 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 10 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 11 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 1)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
  else
    if v.val < 18 then
      if v.val < 15 then
        if v.val < 13 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 14 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 1 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 23 | 1 => 20 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 1 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 16 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 1 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 17 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 1 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 1) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 18))
    else
      if v.val < 21 then
        if v.val < 19 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 20 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 23 | 1 => 1 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 1 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 22 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 1 | 4 => 16 | _ => 17))
        else
          if v.val < 23 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 1 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 19 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 1))

def c24Parent3 (v : Fin 24) : Fin 24 → Fin 24 :=
  if v.val < 12 then
    if v.val < 6 then
      if v.val < 3 then
        if v.val < 1 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 12 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 2 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 5 | 1 => 2 | 2 => 2 | 3 => 2 | 4 => 3 | _ => 4) else (match x.val - 6 with | 0 => 0 | 1 => 13 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 11) else (match x.val - 18 with | 0 => 2 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 4 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 13 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 19 | 3 => 20 | 4 => 16 | _ => 17))
      else
        if v.val < 4 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 14 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 5 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 16 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 1) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 17)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
    else
      if v.val < 9 then
        if v.val < 7 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 11) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 8 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 6 | 1 => 8 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 9 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 10 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 10 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 11 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 1)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 10 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
  else
    if v.val < 18 then
      if v.val < 15 then
        if v.val < 13 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 1 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 14 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 1 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 20 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 1 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 19 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 16 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 1 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 20 | 4 => 16 | _ => 17))
        else
          if v.val < 17 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 1 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 23 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 1) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 22))
    else
      if v.val < 21 then
        if v.val < 19 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
        else
          if v.val < 20 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 1 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 1 | 3 => 15 | 4 => 16 | _ => 17))
      else
        if v.val < 22 then
          fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 1 | 4 => 16 | _ => 17))
        else
          if v.val < 23 then
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 1 | _ => 17))
          else
            fun x => if x.val < 12 then (if x.val < 6 then (match x.val - 0 with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 5 | _ => 0) else (match x.val - 6 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | _ => 5)) else (if x.val < 18 then (match x.val - 12 with | 0 => 7 | 1 => 7 | 2 => 8 | 3 => 9 | 4 => 11 | _ => 6) else (match x.val - 18 with | 0 => 1 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | _ => 1))

def g7AdjFast (a b : Fin 7) : Bool :=
  match a.val with
  | 0 => b.val == 1 || b.val == 4 || b.val == 5
  | 1 => b.val == 0 || b.val == 2 || b.val == 5
  | 2 => b.val == 1 || b.val == 3 || b.val == 6
  | 3 => b.val == 2 || b.val == 4 || b.val == 6
  | 4 => b.val == 0 || b.val == 3
  | 5 => b.val == 0 || b.val == 1
  | 6 => b.val == 2 || b.val == 3
  | _ => false

def g7Parent1 (d : Fin 7) (x : Fin 7) : Fin 7 :=
  if d.val < 3 then
    if d.val < 1 then
      match x.val with | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 1 | _ => 2
    else
      if d.val < 2 then
        match x.val with | 0 => 0 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 0 | _ => 3
      else
        match x.val with | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 4 | 4 => 0 | 5 => 0 | _ => 3
  else
    if d.val < 5 then
      if d.val < 4 then
        match x.val with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | _ => 2
      else
        match x.val with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 0 | _ => 2
    else
      if d.val < 6 then
        match x.val with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 0 | _ => 2
      else
        match x.val with | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 0 | _ => 0

def g7Parent2 (d1 d2 : Fin 7) (x : Fin 7) : Fin 7 :=
  if d1.val * 7 + d2.val < 24 then
    if d1.val * 7 + d2.val < 12 then
      if d1.val * 7 + d2.val < 6 then
        if d1.val * 7 + d2.val < 3 then
          if d1.val * 7 + d2.val < 1 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 2 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
        else
          if d1.val * 7 + d2.val < 4 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 5 then
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 2 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
      else
        if d1.val * 7 + d2.val < 9 then
          if d1.val * 7 + d2.val < 7 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
          else
            if d1.val * 7 + d2.val < 8 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
        else
          if d1.val * 7 + d2.val < 10 then
            match x.val with | 0 => 4 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 11 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
    else
      if d1.val * 7 + d2.val < 18 then
        if d1.val * 7 + d2.val < 15 then
          if d1.val * 7 + d2.val < 13 then
            match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
          else
            if d1.val * 7 + d2.val < 14 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
        else
          if d1.val * 7 + d2.val < 16 then
            match x.val with | 0 => 4 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 17 then
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
      else
        if d1.val * 7 + d2.val < 21 then
          if d1.val * 7 + d2.val < 19 then
            match x.val with | 0 => 5 | 1 => 5 | 2 => 5 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 20 then
              match x.val with | 0 => 4 | 1 => 0 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
        else
          if d1.val * 7 + d2.val < 22 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 23 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
  else
    if d1.val * 7 + d2.val < 36 then
      if d1.val * 7 + d2.val < 30 then
        if d1.val * 7 + d2.val < 27 then
          if d1.val * 7 + d2.val < 25 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 26 then
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 5 | 4 => 5 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 0 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
        else
          if d1.val * 7 + d2.val < 28 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
          else
            if d1.val * 7 + d2.val < 29 then
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
      else
        if d1.val * 7 + d2.val < 33 then
          if d1.val * 7 + d2.val < 31 then
            match x.val with | 0 => 5 | 1 => 5 | 2 => 5 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
          else
            if d1.val * 7 + d2.val < 32 then
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 5 | 4 => 5 | 5 => 5 | _ => 6
            else
              match x.val with | 0 => 5 | 1 => 5 | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5 | _ => 6
        else
          if d1.val * 7 + d2.val < 34 then
            match x.val with | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 6 | 4 => 6 | 5 => 6 | _ => 6
          else
            if d1.val * 7 + d2.val < 35 then
              match x.val with | 0 => 5 | 1 => 5 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 5 | _ => 5
            else
              match x.val with | 0 => 4 | 1 => 2 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
    else
      if d1.val * 7 + d2.val < 42 then
        if d1.val * 7 + d2.val < 39 then
          if d1.val * 7 + d2.val < 37 then
            match x.val with | 0 => 4 | 1 => 4 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
          else
            if d1.val * 7 + d2.val < 38 then
              match x.val with | 0 => 4 | 1 => 0 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 0 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
        else
          if d1.val * 7 + d2.val < 40 then
            match x.val with | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 6 | 4 => 6 | 5 => 6 | _ => 6
          else
            if d1.val * 7 + d2.val < 41 then
              match x.val with | 0 => 4 | 1 => 0 | 2 => 6 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 6
            else
              match x.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 4
      else
        if d1.val * 7 + d2.val < 45 then
          if d1.val * 7 + d2.val < 43 then
            match x.val with | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
          else
            if d1.val * 7 + d2.val < 44 then
              match x.val with | 0 => 4 | 1 => 4 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
        else
          if d1.val * 7 + d2.val < 47 then
            if d1.val * 7 + d2.val < 46 then
              match x.val with | 0 => 4 | 1 => 5 | 2 => 1 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4
            else
              match x.val with | 0 => 5 | 1 => 5 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 5 | _ => 5
          else
            if d1.val * 7 + d2.val < 48 then
              match x.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 4 | _ => 4
            else
              match x.val with | 0 => 4 | 1 => 5 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 5 | _ => 4

def g168Nbrs (u : Fin 168) : Fin 168 × Fin 168 × Fin 168 :=
  if u.val < 84 then
    if u.val < 42 then
      if u.val < 21 then
        if u.val < 10 then
          if u.val < 5 then
            if u.val < 2 then
              if u.val < 1 then
                (1, 4, 5)
              else
                (0, 2, 5)
            else
              if u.val < 3 then
                (1, 3, 6)
              else
                if u.val < 4 then
                  (2, 4, 6)
                else
                  (0, 3, 13)
          else
            if u.val < 7 then
              if u.val < 6 then
                (0, 1, 47)
              else
                (2, 3, 39)
            else
              if u.val < 8 then
                (8, 11, 12)
              else
                if u.val < 9 then
                  (7, 9, 12)
                else
                  (8, 10, 13)
        else
          if u.val < 15 then
            if u.val < 12 then
              if u.val < 11 then
                (9, 11, 13)
              else
                (7, 10, 20)
            else
              if u.val < 13 then
                (7, 8, 54)
              else
                if u.val < 14 then
                  (4, 9, 10)
                else
                  (15, 18, 19)
          else
            if u.val < 18 then
              if u.val < 16 then
                (14, 16, 19)
              else
                if u.val < 17 then
                  (15, 17, 20)
                else
                  (16, 18, 20)
            else
              if u.val < 19 then
                (14, 17, 27)
              else
                if u.val < 20 then
                  (14, 15, 61)
                else
                  (11, 16, 17)
      else
        if u.val < 31 then
          if u.val < 26 then
            if u.val < 23 then
              if u.val < 22 then
                (22, 25, 26)
              else
                (21, 23, 26)
            else
              if u.val < 24 then
                (22, 24, 27)
              else
                if u.val < 25 then
                  (23, 25, 27)
                else
                  (21, 24, 34)
          else
            if u.val < 28 then
              if u.val < 27 then
                (21, 22, 68)
              else
                (18, 23, 24)
            else
              if u.val < 29 then
                (29, 32, 33)
              else
                if u.val < 30 then
                  (28, 30, 33)
                else
                  (29, 31, 34)
        else
          if u.val < 36 then
            if u.val < 33 then
              if u.val < 32 then
                (30, 32, 34)
              else
                (28, 31, 41)
            else
              if u.val < 34 then
                (28, 29, 75)
              else
                if u.val < 35 then
                  (25, 30, 31)
                else
                  (36, 39, 40)
          else
            if u.val < 39 then
              if u.val < 37 then
                (35, 37, 40)
              else
                if u.val < 38 then
                  (36, 38, 41)
                else
                  (37, 39, 41)
            else
              if u.val < 40 then
                (6, 35, 38)
              else
                if u.val < 41 then
                  (35, 36, 82)
                else
                  (32, 37, 38)
    else
      if u.val < 63 then
        if u.val < 52 then
          if u.val < 47 then
            if u.val < 44 then
              if u.val < 43 then
                (43, 46, 47)
              else
                (42, 44, 47)
            else
              if u.val < 45 then
                (43, 45, 48)
              else
                if u.val < 46 then
                  (44, 46, 48)
                else
                  (42, 45, 124)
          else
            if u.val < 49 then
              if u.val < 48 then
                (5, 42, 43)
              else
                (44, 45, 88)
            else
              if u.val < 50 then
                (50, 53, 54)
              else
                if u.val < 51 then
                  (49, 51, 54)
                else
                  (50, 52, 55)
        else
          if u.val < 57 then
            if u.val < 54 then
              if u.val < 53 then
                (51, 53, 55)
              else
                (49, 52, 89)
            else
              if u.val < 55 then
                (12, 49, 50)
              else
                if u.val < 56 then
                  (51, 52, 95)
                else
                  (57, 60, 61)
          else
            if u.val < 60 then
              if u.val < 58 then
                (56, 58, 61)
              else
                if u.val < 59 then
                  (57, 59, 62)
                else
                  (58, 60, 62)
            else
              if u.val < 61 then
                (56, 59, 96)
              else
                if u.val < 62 then
                  (19, 56, 57)
                else
                  (58, 59, 102)
      else
        if u.val < 73 then
          if u.val < 68 then
            if u.val < 65 then
              if u.val < 64 then
                (64, 67, 68)
              else
                (63, 65, 68)
            else
              if u.val < 66 then
                (64, 66, 69)
              else
                if u.val < 67 then
                  (65, 67, 69)
                else
                  (63, 66, 103)
          else
            if u.val < 70 then
              if u.val < 69 then
                (26, 63, 64)
              else
                (65, 66, 109)
            else
              if u.val < 71 then
                (71, 74, 75)
              else
                if u.val < 72 then
                  (70, 72, 75)
                else
                  (71, 73, 76)
        else
          if u.val < 78 then
            if u.val < 75 then
              if u.val < 74 then
                (72, 74, 76)
              else
                (70, 73, 110)
            else
              if u.val < 76 then
                (33, 70, 71)
              else
                if u.val < 77 then
                  (72, 73, 116)
                else
                  (78, 81, 82)
          else
            if u.val < 81 then
              if u.val < 79 then
                (77, 79, 82)
              else
                if u.val < 80 then
                  (78, 80, 83)
                else
                  (79, 81, 83)
            else
              if u.val < 82 then
                (77, 80, 117)
              else
                if u.val < 83 then
                  (40, 77, 78)
                else
                  (79, 80, 123)
  else
    if u.val < 126 then
      if u.val < 105 then
        if u.val < 94 then
          if u.val < 89 then
            if u.val < 86 then
              if u.val < 85 then
                (85, 88, 89)
              else
                (84, 86, 89)
            else
              if u.val < 87 then
                (85, 87, 90)
              else
                if u.val < 88 then
                  (86, 88, 90)
                else
                  (48, 84, 87)
          else
            if u.val < 91 then
              if u.val < 90 then
                (53, 84, 85)
              else
                (86, 87, 131)
            else
              if u.val < 92 then
                (92, 95, 96)
              else
                if u.val < 93 then
                  (91, 93, 96)
                else
                  (92, 94, 97)
        else
          if u.val < 99 then
            if u.val < 96 then
              if u.val < 95 then
                (93, 95, 97)
              else
                (55, 91, 94)
            else
              if u.val < 97 then
                (60, 91, 92)
              else
                if u.val < 98 then
                  (93, 94, 138)
                else
                  (99, 102, 103)
          else
            if u.val < 102 then
              if u.val < 100 then
                (98, 100, 103)
              else
                if u.val < 101 then
                  (99, 101, 104)
                else
                  (100, 102, 104)
            else
              if u.val < 103 then
                (62, 98, 101)
              else
                if u.val < 104 then
                  (67, 98, 99)
                else
                  (100, 101, 145)
      else
        if u.val < 115 then
          if u.val < 110 then
            if u.val < 107 then
              if u.val < 106 then
                (106, 109, 110)
              else
                (105, 107, 110)
            else
              if u.val < 108 then
                (106, 108, 111)
              else
                if u.val < 109 then
                  (107, 109, 111)
                else
                  (69, 105, 108)
          else
            if u.val < 112 then
              if u.val < 111 then
                (74, 105, 106)
              else
                (107, 108, 152)
            else
              if u.val < 113 then
                (113, 116, 117)
              else
                if u.val < 114 then
                  (112, 114, 117)
                else
                  (113, 115, 118)
        else
          if u.val < 120 then
            if u.val < 117 then
              if u.val < 116 then
                (114, 116, 118)
              else
                (76, 112, 115)
            else
              if u.val < 118 then
                (81, 112, 113)
              else
                if u.val < 119 then
                  (114, 115, 159)
                else
                  (120, 123, 124)
          else
            if u.val < 123 then
              if u.val < 121 then
                (119, 121, 124)
              else
                if u.val < 122 then
                  (120, 122, 125)
                else
                  (121, 123, 125)
            else
              if u.val < 124 then
                (83, 119, 122)
              else
                if u.val < 125 then
                  (46, 119, 120)
                else
                  (121, 122, 166)
    else
      if u.val < 147 then
        if u.val < 136 then
          if u.val < 131 then
            if u.val < 128 then
              if u.val < 127 then
                (127, 130, 131)
              else
                (126, 128, 131)
            else
              if u.val < 129 then
                (127, 129, 132)
              else
                if u.val < 130 then
                  (128, 130, 132)
                else
                  (126, 129, 167)
          else
            if u.val < 133 then
              if u.val < 132 then
                (90, 126, 127)
              else
                (128, 129, 137)
            else
              if u.val < 134 then
                (134, 137, 138)
              else
                if u.val < 135 then
                  (133, 135, 138)
                else
                  (134, 136, 139)
        else
          if u.val < 141 then
            if u.val < 138 then
              if u.val < 137 then
                (135, 137, 139)
              else
                (132, 133, 136)
            else
              if u.val < 139 then
                (97, 133, 134)
              else
                if u.val < 140 then
                  (135, 136, 144)
                else
                  (141, 144, 145)
          else
            if u.val < 144 then
              if u.val < 142 then
                (140, 142, 145)
              else
                if u.val < 143 then
                  (141, 143, 146)
                else
                  (142, 144, 146)
            else
              if u.val < 145 then
                (139, 140, 143)
              else
                if u.val < 146 then
                  (104, 140, 141)
                else
                  (142, 143, 151)
      else
        if u.val < 157 then
          if u.val < 152 then
            if u.val < 149 then
              if u.val < 148 then
                (148, 151, 152)
              else
                (147, 149, 152)
            else
              if u.val < 150 then
                (148, 150, 153)
              else
                if u.val < 151 then
                  (149, 151, 153)
                else
                  (146, 147, 150)
          else
            if u.val < 154 then
              if u.val < 153 then
                (111, 147, 148)
              else
                (149, 150, 158)
            else
              if u.val < 155 then
                (155, 158, 159)
              else
                if u.val < 156 then
                  (154, 156, 159)
                else
                  (155, 157, 160)
        else
          if u.val < 162 then
            if u.val < 159 then
              if u.val < 158 then
                (156, 158, 160)
              else
                (153, 154, 157)
            else
              if u.val < 160 then
                (118, 154, 155)
              else
                if u.val < 161 then
                  (156, 157, 165)
                else
                  (162, 165, 166)
          else
            if u.val < 165 then
              if u.val < 163 then
                (161, 163, 166)
              else
                if u.val < 164 then
                  (162, 164, 167)
                else
                  (163, 165, 167)
            else
              if u.val < 166 then
                (160, 161, 164)
              else
                if u.val < 167 then
                  (125, 161, 162)
                else
                  (130, 163, 164)

def g168Faces : List (List (Fin 168)) := [
  [0, 4, 3, 2, 1],
  [5, 0, 1],
  [6, 2, 3],
  [7, 11, 10, 9, 8],
  [12, 7, 8],
  [13, 9, 10],
  [14, 18, 17, 16, 15],
  [19, 14, 15],
  [20, 16, 17],
  [21, 25, 24, 23, 22],
  [26, 21, 22],
  [27, 23, 24],
  [28, 32, 31, 30, 29],
  [33, 28, 29],
  [34, 30, 31],
  [35, 39, 38, 37, 36],
  [40, 35, 36],
  [41, 37, 38],
  [42, 46, 45, 44, 43],
  [47, 42, 43],
  [48, 44, 45],
  [49, 53, 52, 51, 50],
  [54, 49, 50],
  [55, 51, 52],
  [56, 60, 59, 58, 57],
  [61, 56, 57],
  [62, 58, 59],
  [63, 67, 66, 65, 64],
  [68, 63, 64],
  [69, 65, 66],
  [70, 74, 73, 72, 71],
  [75, 70, 71],
  [76, 72, 73],
  [77, 81, 80, 79, 78],
  [82, 77, 78],
  [83, 79, 80],
  [84, 88, 87, 86, 85],
  [89, 84, 85],
  [90, 86, 87],
  [91, 95, 94, 93, 92],
  [96, 91, 92],
  [97, 93, 94],
  [98, 102, 101, 100, 99],
  [103, 98, 99],
  [104, 100, 101],
  [105, 109, 108, 107, 106],
  [110, 105, 106],
  [111, 107, 108],
  [112, 116, 115, 114, 113],
  [117, 112, 113],
  [118, 114, 115],
  [119, 123, 122, 121, 120],
  [124, 119, 120],
  [125, 121, 122],
  [126, 130, 129, 128, 127],
  [131, 126, 127],
  [132, 128, 129],
  [133, 137, 136, 135, 134],
  [138, 133, 134],
  [139, 135, 136],
  [140, 144, 143, 142, 141],
  [145, 140, 141],
  [146, 142, 143],
  [147, 151, 150, 149, 148],
  [152, 147, 148],
  [153, 149, 150],
  [154, 158, 157, 156, 155],
  [159, 154, 155],
  [160, 156, 157],
  [161, 165, 164, 163, 162],
  [166, 161, 162],
  [167, 163, 164],
  [6, 3, 4, 13, 10, 11, 20, 17, 18, 27, 24, 25, 34, 31, 32, 41, 38, 39],
  [167, 164, 165, 160, 157, 158, 153, 150, 151, 146, 143, 144, 139, 136, 137, 132, 129, 130],
  [4, 0, 5, 47, 43, 44, 48, 88, 84, 89, 53, 49, 54, 12, 8, 9, 13],
  [131, 127, 128, 132, 137, 133, 138, 97, 94, 95, 55, 52, 53, 89, 85, 86, 90],
  [11, 7, 12, 54, 50, 51, 55, 95, 91, 96, 60, 56, 61, 19, 15, 16, 20],
  [138, 134, 135, 139, 144, 140, 145, 104, 101, 102, 62, 59, 60, 96, 92, 93, 97],
  [18, 14, 19, 61, 57, 58, 62, 102, 98, 103, 67, 63, 68, 26, 22, 23, 27],
  [145, 141, 142, 146, 151, 147, 152, 111, 108, 109, 69, 66, 67, 103, 99, 100, 104],
  [25, 21, 26, 68, 64, 65, 69, 109, 105, 110, 74, 70, 75, 33, 29, 30, 34],
  [152, 148, 149, 153, 158, 154, 159, 118, 115, 116, 76, 73, 74, 110, 106, 107, 111],
  [32, 28, 33, 75, 71, 72, 76, 116, 112, 117, 81, 77, 82, 40, 36, 37, 41],
  [159, 155, 156, 160, 165, 161, 166, 125, 122, 123, 83, 80, 81, 117, 113, 114, 118],
  [39, 35, 40, 82, 78, 79, 83, 123, 119, 124, 46, 42, 47, 5, 1, 2, 6],
  [166, 162, 163, 167, 130, 126, 131, 90, 87, 88, 48, 45, 46, 124, 120, 121, 125],
]

def g168DartLocTriple (u : Fin 168) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) :=
  if u.val < 84 then
    if u.val < 42 then
      if u.val < 21 then
        if u.val < 10 then
          if u.val < 5 then
            if u.val < 2 then
              if u.val < 1 then
                ((1, 1), (0, 0), (74, 1))
              else
                ((0, 4), (84, 14), (1, 2))
            else
              if u.val < 3 then
                ((0, 3), (2, 1), (84, 15))
              else
                if u.val < 4 then
                  ((0, 2), (72, 1), (2, 2))
                else
                  ((74, 0), (0, 1), (72, 2))
          else
            if u.val < 7 then
              if u.val < 6 then
                ((1, 0), (84, 13), (74, 2))
              else
                ((2, 0), (72, 0), (84, 16))
            else
              if u.val < 8 then
                ((4, 1), (3, 0), (76, 1))
              else
                if u.val < 9 then
                  ((3, 4), (74, 14), (4, 2))
                else
                  ((3, 3), (5, 1), (74, 15))
        else
          if u.val < 15 then
            if u.val < 12 then
              if u.val < 11 then
                ((3, 2), (72, 4), (5, 2))
              else
                ((76, 0), (3, 1), (72, 5))
            else
              if u.val < 13 then
                ((4, 0), (74, 13), (76, 2))
              else
                if u.val < 14 then
                  ((74, 16), (5, 0), (72, 3))
                else
                  ((7, 1), (6, 0), (78, 1))
          else
            if u.val < 18 then
              if u.val < 16 then
                ((6, 4), (76, 14), (7, 2))
              else
                if u.val < 17 then
                  ((6, 3), (8, 1), (76, 15))
                else
                  ((6, 2), (72, 7), (8, 2))
            else
              if u.val < 19 then
                ((78, 0), (6, 1), (72, 8))
              else
                if u.val < 20 then
                  ((7, 0), (76, 13), (78, 2))
                else
                  ((76, 16), (8, 0), (72, 6))
      else
        if u.val < 31 then
          if u.val < 26 then
            if u.val < 23 then
              if u.val < 22 then
                ((10, 1), (9, 0), (80, 1))
              else
                ((9, 4), (78, 14), (10, 2))
            else
              if u.val < 24 then
                ((9, 3), (11, 1), (78, 15))
              else
                if u.val < 25 then
                  ((9, 2), (72, 10), (11, 2))
                else
                  ((80, 0), (9, 1), (72, 11))
          else
            if u.val < 28 then
              if u.val < 27 then
                ((10, 0), (78, 13), (80, 2))
              else
                ((78, 16), (11, 0), (72, 9))
            else
              if u.val < 29 then
                ((13, 1), (12, 0), (82, 1))
              else
                if u.val < 30 then
                  ((12, 4), (80, 14), (13, 2))
                else
                  ((12, 3), (14, 1), (80, 15))
        else
          if u.val < 36 then
            if u.val < 33 then
              if u.val < 32 then
                ((12, 2), (72, 13), (14, 2))
              else
                ((82, 0), (12, 1), (72, 14))
            else
              if u.val < 34 then
                ((13, 0), (80, 13), (82, 2))
              else
                if u.val < 35 then
                  ((80, 16), (14, 0), (72, 12))
                else
                  ((16, 1), (15, 0), (84, 1))
          else
            if u.val < 39 then
              if u.val < 37 then
                ((15, 4), (82, 14), (16, 2))
              else
                if u.val < 38 then
                  ((15, 3), (17, 1), (82, 15))
                else
                  ((15, 2), (72, 16), (17, 2))
            else
              if u.val < 40 then
                ((72, 17), (84, 0), (15, 1))
              else
                if u.val < 41 then
                  ((16, 0), (82, 13), (84, 2))
                else
                  ((82, 16), (17, 0), (72, 15))
    else
      if u.val < 63 then
        if u.val < 52 then
          if u.val < 47 then
            if u.val < 44 then
              if u.val < 43 then
                ((19, 1), (18, 0), (84, 11))
              else
                ((18, 4), (74, 4), (19, 2))
            else
              if u.val < 45 then
                ((18, 3), (20, 1), (74, 5))
              else
                if u.val < 46 then
                  ((18, 2), (85, 11), (20, 2))
                else
                  ((84, 10), (18, 1), (85, 12))
          else
            if u.val < 49 then
              if u.val < 48 then
                ((84, 12), (19, 0), (74, 3))
              else
                ((20, 0), (85, 10), (74, 6))
            else
              if u.val < 50 then
                ((22, 1), (21, 0), (74, 11))
              else
                if u.val < 51 then
                  ((21, 4), (76, 4), (22, 2))
                else
                  ((21, 3), (23, 1), (76, 5))
        else
          if u.val < 57 then
            if u.val < 54 then
              if u.val < 53 then
                ((21, 2), (75, 11), (23, 2))
              else
                ((74, 10), (21, 1), (75, 12))
            else
              if u.val < 55 then
                ((74, 12), (22, 0), (76, 3))
              else
                if u.val < 56 then
                  ((23, 0), (75, 10), (76, 6))
                else
                  ((25, 1), (24, 0), (76, 11))
          else
            if u.val < 60 then
              if u.val < 58 then
                ((24, 4), (78, 4), (25, 2))
              else
                if u.val < 59 then
                  ((24, 3), (26, 1), (78, 5))
                else
                  ((24, 2), (77, 11), (26, 2))
            else
              if u.val < 61 then
                ((76, 10), (24, 1), (77, 12))
              else
                if u.val < 62 then
                  ((76, 12), (25, 0), (78, 3))
                else
                  ((26, 0), (77, 10), (78, 6))
      else
        if u.val < 73 then
          if u.val < 68 then
            if u.val < 65 then
              if u.val < 64 then
                ((28, 1), (27, 0), (78, 11))
              else
                ((27, 4), (80, 4), (28, 2))
            else
              if u.val < 66 then
                ((27, 3), (29, 1), (80, 5))
              else
                if u.val < 67 then
                  ((27, 2), (79, 11), (29, 2))
                else
                  ((78, 10), (27, 1), (79, 12))
          else
            if u.val < 70 then
              if u.val < 69 then
                ((78, 12), (28, 0), (80, 3))
              else
                ((29, 0), (79, 10), (80, 6))
            else
              if u.val < 71 then
                ((31, 1), (30, 0), (80, 11))
              else
                if u.val < 72 then
                  ((30, 4), (82, 4), (31, 2))
                else
                  ((30, 3), (32, 1), (82, 5))
        else
          if u.val < 78 then
            if u.val < 75 then
              if u.val < 74 then
                ((30, 2), (81, 11), (32, 2))
              else
                ((80, 10), (30, 1), (81, 12))
            else
              if u.val < 76 then
                ((80, 12), (31, 0), (82, 3))
              else
                if u.val < 77 then
                  ((32, 0), (81, 10), (82, 6))
                else
                  ((34, 1), (33, 0), (82, 11))
          else
            if u.val < 81 then
              if u.val < 79 then
                ((33, 4), (84, 4), (34, 2))
              else
                if u.val < 80 then
                  ((33, 3), (35, 1), (84, 5))
                else
                  ((33, 2), (83, 11), (35, 2))
            else
              if u.val < 82 then
                ((82, 10), (33, 1), (83, 12))
              else
                if u.val < 83 then
                  ((82, 12), (34, 0), (84, 3))
                else
                  ((35, 0), (83, 10), (84, 6))
  else
    if u.val < 126 then
      if u.val < 105 then
        if u.val < 94 then
          if u.val < 89 then
            if u.val < 86 then
              if u.val < 85 then
                ((37, 1), (36, 0), (74, 8))
              else
                ((36, 4), (75, 14), (37, 2))
            else
              if u.val < 87 then
                ((36, 3), (38, 1), (75, 15))
              else
                if u.val < 88 then
                  ((36, 2), (85, 8), (38, 2))
                else
                  ((85, 9), (74, 7), (36, 1))
          else
            if u.val < 91 then
              if u.val < 90 then
                ((74, 9), (37, 0), (75, 13))
              else
                ((38, 0), (85, 7), (75, 16))
            else
              if u.val < 92 then
                ((40, 1), (39, 0), (76, 8))
              else
                if u.val < 93 then
                  ((39, 4), (77, 14), (40, 2))
                else
                  ((39, 3), (41, 1), (77, 15))
        else
          if u.val < 99 then
            if u.val < 96 then
              if u.val < 95 then
                ((39, 2), (75, 8), (41, 2))
              else
                ((75, 9), (76, 7), (39, 1))
            else
              if u.val < 97 then
                ((76, 9), (40, 0), (77, 13))
              else
                if u.val < 98 then
                  ((41, 0), (75, 7), (77, 16))
                else
                  ((43, 1), (42, 0), (78, 8))
          else
            if u.val < 102 then
              if u.val < 100 then
                ((42, 4), (79, 14), (43, 2))
              else
                if u.val < 101 then
                  ((42, 3), (44, 1), (79, 15))
                else
                  ((42, 2), (77, 8), (44, 2))
            else
              if u.val < 103 then
                ((77, 9), (78, 7), (42, 1))
              else
                if u.val < 104 then
                  ((78, 9), (43, 0), (79, 13))
                else
                  ((44, 0), (77, 7), (79, 16))
      else
        if u.val < 115 then
          if u.val < 110 then
            if u.val < 107 then
              if u.val < 106 then
                ((46, 1), (45, 0), (80, 8))
              else
                ((45, 4), (81, 14), (46, 2))
            else
              if u.val < 108 then
                ((45, 3), (47, 1), (81, 15))
              else
                if u.val < 109 then
                  ((45, 2), (79, 8), (47, 2))
                else
                  ((79, 9), (80, 7), (45, 1))
          else
            if u.val < 112 then
              if u.val < 111 then
                ((80, 9), (46, 0), (81, 13))
              else
                ((47, 0), (79, 7), (81, 16))
            else
              if u.val < 113 then
                ((49, 1), (48, 0), (82, 8))
              else
                if u.val < 114 then
                  ((48, 4), (83, 14), (49, 2))
                else
                  ((48, 3), (50, 1), (83, 15))
        else
          if u.val < 120 then
            if u.val < 117 then
              if u.val < 116 then
                ((48, 2), (81, 8), (50, 2))
              else
                ((81, 9), (82, 7), (48, 1))
            else
              if u.val < 118 then
                ((82, 9), (49, 0), (83, 13))
              else
                if u.val < 119 then
                  ((50, 0), (81, 7), (83, 16))
                else
                  ((52, 1), (51, 0), (84, 8))
          else
            if u.val < 123 then
              if u.val < 121 then
                ((51, 4), (85, 14), (52, 2))
              else
                if u.val < 122 then
                  ((51, 3), (53, 1), (85, 15))
                else
                  ((51, 2), (83, 8), (53, 2))
            else
              if u.val < 124 then
                ((83, 9), (84, 7), (51, 1))
              else
                if u.val < 125 then
                  ((84, 9), (52, 0), (85, 13))
                else
                  ((53, 0), (83, 7), (85, 16))
    else
      if u.val < 147 then
        if u.val < 136 then
          if u.val < 131 then
            if u.val < 128 then
              if u.val < 127 then
                ((55, 1), (54, 0), (85, 5))
              else
                ((54, 4), (75, 1), (55, 2))
            else
              if u.val < 129 then
                ((54, 3), (56, 1), (75, 2))
              else
                if u.val < 130 then
                  ((54, 2), (73, 16), (56, 2))
                else
                  ((85, 4), (54, 1), (73, 17))
          else
            if u.val < 133 then
              if u.val < 132 then
                ((85, 6), (55, 0), (75, 0))
              else
                ((56, 0), (73, 15), (75, 3))
            else
              if u.val < 134 then
                ((58, 1), (57, 0), (75, 5))
              else
                if u.val < 135 then
                  ((57, 4), (77, 1), (58, 2))
                else
                  ((57, 3), (59, 1), (77, 2))
        else
          if u.val < 141 then
            if u.val < 138 then
              if u.val < 137 then
                ((57, 2), (73, 13), (59, 2))
              else
                ((73, 14), (75, 4), (57, 1))
            else
              if u.val < 139 then
                ((75, 6), (58, 0), (77, 0))
              else
                if u.val < 140 then
                  ((59, 0), (73, 12), (77, 3))
                else
                  ((61, 1), (60, 0), (77, 5))
          else
            if u.val < 144 then
              if u.val < 142 then
                ((60, 4), (79, 1), (61, 2))
              else
                if u.val < 143 then
                  ((60, 3), (62, 1), (79, 2))
                else
                  ((60, 2), (73, 10), (62, 2))
            else
              if u.val < 145 then
                ((73, 11), (77, 4), (60, 1))
              else
                if u.val < 146 then
                  ((77, 6), (61, 0), (79, 0))
                else
                  ((62, 0), (73, 9), (79, 3))
      else
        if u.val < 157 then
          if u.val < 152 then
            if u.val < 149 then
              if u.val < 148 then
                ((64, 1), (63, 0), (79, 5))
              else
                ((63, 4), (81, 1), (64, 2))
            else
              if u.val < 150 then
                ((63, 3), (65, 1), (81, 2))
              else
                if u.val < 151 then
                  ((63, 2), (73, 7), (65, 2))
                else
                  ((73, 8), (79, 4), (63, 1))
          else
            if u.val < 154 then
              if u.val < 153 then
                ((79, 6), (64, 0), (81, 0))
              else
                ((65, 0), (73, 6), (81, 3))
            else
              if u.val < 155 then
                ((67, 1), (66, 0), (81, 5))
              else
                if u.val < 156 then
                  ((66, 4), (83, 1), (67, 2))
                else
                  ((66, 3), (68, 1), (83, 2))
        else
          if u.val < 162 then
            if u.val < 159 then
              if u.val < 158 then
                ((66, 2), (73, 4), (68, 2))
              else
                ((73, 5), (81, 4), (66, 1))
            else
              if u.val < 160 then
                ((81, 6), (67, 0), (83, 0))
              else
                if u.val < 161 then
                  ((68, 0), (73, 3), (83, 3))
                else
                  ((70, 1), (69, 0), (83, 5))
          else
            if u.val < 165 then
              if u.val < 163 then
                ((69, 4), (85, 1), (70, 2))
              else
                if u.val < 164 then
                  ((69, 3), (71, 1), (85, 2))
                else
                  ((69, 2), (73, 1), (71, 2))
            else
              if u.val < 166 then
                ((73, 2), (83, 4), (69, 1))
              else
                if u.val < 167 then
                  ((83, 6), (70, 0), (85, 0))
                else
                  ((85, 3), (71, 0), (73, 0))

def g168DartLoc (u : Fin 168) (slot : Fin 3) : Nat × Nat :=
  let t := g168DartLocTriple u
  match slot.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def g168C32 : List (Fin 168) := [5, 0, 1, 2, 6, 39, 35, 40, 82, 78, 79, 83, 123, 122, 125, 166, 162, 163, 167, 130, 126, 131, 90, 87, 88, 48, 44, 45, 46, 42, 43, 47]

def c60Nbrs (u : Fin 60) : Fin 60 × Fin 60 × Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            (2, 4, 5)
          else
            if u.val < 2 then
              (3, 4, 20)
            else
              (0, 3, 25)
        else
          if u.val < 5 then
            if u.val < 4 then
              (1, 2, 45)
            else
              (0, 1, 50)
          else
            if u.val < 6 then
              (0, 7, 9)
            else
              (8, 9, 10)
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              (5, 8, 26)
            else
              (6, 7, 30)
          else
            if u.val < 10 then
              (5, 6, 51)
            else
              (6, 12, 14)
        else
          if u.val < 13 then
            if u.val < 12 then
              (13, 14, 15)
            else
              (10, 13, 31)
          else
            if u.val < 14 then
              (11, 12, 35)
            else
              (10, 11, 52)
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            (11, 17, 19)
          else
            if u.val < 17 then
              (18, 19, 21)
            else
              (15, 18, 36)
        else
          if u.val < 20 then
            if u.val < 19 then
              (16, 17, 40)
            else
              (15, 16, 53)
          else
            if u.val < 21 then
              (1, 23, 24)
            else
              (16, 22, 24)
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              (21, 23, 41)
            else
              (20, 22, 46)
          else
            if u.val < 25 then
              (20, 21, 54)
            else
              (2, 26, 28)
        else
          if u.val < 28 then
            if u.val < 27 then
              (7, 25, 27)
            else
              (26, 29, 32)
          else
            if u.val < 29 then
              (25, 29, 47)
            else
              (27, 28, 55)
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            (8, 31, 32)
          else
            if u.val < 32 then
              (12, 30, 33)
            else
              (27, 30, 34)
        else
          if u.val < 35 then
            if u.val < 34 then
              (31, 34, 37)
            else
              (32, 33, 56)
          else
            if u.val < 36 then
              (13, 36, 37)
            else
              (17, 35, 38)
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              (33, 35, 39)
            else
              (36, 39, 42)
          else
            if u.val < 40 then
              (37, 38, 57)
            else
              (18, 41, 42)
        else
          if u.val < 43 then
            if u.val < 42 then
              (22, 40, 43)
            else
              (38, 40, 44)
          else
            if u.val < 44 then
              (41, 44, 48)
            else
              (42, 43, 58)
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            (3, 46, 47)
          else
            if u.val < 47 then
              (23, 45, 48)
            else
              (28, 45, 49)
        else
          if u.val < 50 then
            if u.val < 49 then
              (43, 46, 49)
            else
              (47, 48, 59)
          else
            if u.val < 51 then
              (4, 51, 54)
            else
              (9, 50, 52)
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              (14, 51, 53)
            else
              (19, 52, 54)
          else
            if u.val < 55 then
              (24, 50, 53)
            else
              (29, 56, 59)
        else
          if u.val < 58 then
            if u.val < 57 then
              (34, 55, 57)
            else
              (39, 56, 58)
          else
            if u.val < 59 then
              (44, 57, 59)
            else
              (49, 55, 58)

def c60Faces : List (List (Fin 60)) := [
  [0, 4, 1, 3, 2],
  [9, 5, 7, 8, 6],
  [14, 10, 12, 13, 11],
  [19, 15, 17, 18, 16],
  [24, 21, 22, 23, 20],
  [26, 25, 28, 29, 27],
  [30, 32, 34, 33, 31],
  [35, 37, 39, 38, 36],
  [40, 42, 44, 43, 41],
  [46, 48, 49, 47, 45],
  [50, 51, 52, 53, 54],
  [56, 55, 59, 58, 57],
  [50, 4, 0, 5, 9, 51],
  [5, 0, 2, 25, 26, 7],
  [7, 26, 27, 32, 30, 8],
  [56, 34, 32, 27, 29, 55],
  [51, 9, 6, 10, 14, 52],
  [10, 6, 8, 30, 31, 12],
  [12, 31, 33, 37, 35, 13],
  [57, 39, 37, 33, 34, 56],
  [52, 14, 11, 15, 19, 53],
  [15, 11, 13, 35, 36, 17],
  [17, 36, 38, 42, 40, 18],
  [58, 44, 42, 38, 39, 57],
  [53, 19, 16, 21, 24, 54],
  [21, 16, 18, 40, 41, 22],
  [22, 41, 43, 48, 46, 23],
  [59, 49, 48, 43, 44, 58],
  [54, 24, 20, 1, 4, 50],
  [1, 20, 23, 46, 45, 3],
  [3, 45, 47, 28, 25, 2],
  [55, 29, 28, 47, 49, 59],
]

def c60DartLocTriple (u : Fin 60) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            ((13, 1), (0, 0), (12, 2))
          else
            if u.val < 2 then
              ((0, 2), (28, 3), (29, 0))
            else
              ((0, 4), (30, 5), (13, 2))
        else
          if u.val < 5 then
            if u.val < 4 then
              ((29, 5), (0, 3), (30, 0))
            else
              ((12, 1), (0, 1), (28, 4))
          else
            if u.val < 6 then
              ((13, 0), (1, 1), (12, 3))
            else
              ((17, 1), (1, 4), (16, 2))
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              ((13, 5), (1, 2), (14, 0))
            else
              ((1, 3), (14, 5), (17, 2))
          else
            if u.val < 10 then
              ((1, 0), (16, 1), (12, 4))
            else
              ((17, 0), (2, 1), (16, 3))
        else
          if u.val < 13 then
            if u.val < 12 then
              ((21, 1), (2, 4), (20, 2))
            else
              ((17, 5), (2, 2), (18, 0))
          else
            if u.val < 14 then
              ((2, 3), (18, 5), (21, 2))
            else
              ((2, 0), (20, 1), (16, 4))
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            ((21, 0), (3, 1), (20, 3))
          else
            if u.val < 17 then
              ((25, 1), (3, 4), (24, 2))
            else
              ((21, 5), (3, 2), (22, 0))
        else
          if u.val < 20 then
            if u.val < 19 then
              ((3, 3), (22, 5), (25, 2))
            else
              ((3, 0), (24, 1), (20, 4))
          else
            if u.val < 21 then
              ((28, 2), (29, 1), (4, 4))
            else
              ((25, 0), (4, 1), (24, 3))
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              ((25, 5), (4, 2), (26, 0))
            else
              ((4, 3), (26, 5), (29, 2))
          else
            if u.val < 25 then
              ((28, 1), (4, 0), (24, 4))
            else
              ((30, 4), (13, 3), (5, 1))
        else
          if u.val < 28 then
            if u.val < 27 then
              ((13, 4), (5, 0), (14, 1))
            else
              ((5, 4), (15, 3), (14, 2))
          else
            if u.val < 29 then
              ((30, 3), (5, 2), (31, 2))
            else
              ((5, 3), (31, 1), (15, 4))
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            ((14, 4), (17, 3), (6, 0))
          else
            if u.val < 32 then
              ((17, 4), (6, 4), (18, 1))
            else
              ((15, 2), (14, 3), (6, 1))
        else
          if u.val < 35 then
            if u.val < 34 then
              ((6, 3), (19, 3), (18, 2))
            else
              ((15, 1), (6, 2), (19, 4))
          else
            if u.val < 36 then
              ((18, 4), (21, 3), (7, 0))
            else
              ((21, 4), (7, 4), (22, 1))
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              ((19, 2), (18, 3), (7, 1))
            else
              ((7, 3), (23, 3), (22, 2))
          else
            if u.val < 40 then
              ((19, 1), (7, 2), (23, 4))
            else
              ((22, 4), (25, 3), (8, 0))
        else
          if u.val < 43 then
            if u.val < 42 then
              ((25, 4), (8, 4), (26, 1))
            else
              ((23, 2), (22, 3), (8, 1))
          else
            if u.val < 44 then
              ((8, 3), (27, 3), (26, 2))
            else
              ((23, 1), (8, 2), (27, 4))
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            ((29, 4), (9, 4), (30, 1))
          else
            if u.val < 47 then
              ((26, 4), (29, 3), (9, 0))
            else
              ((30, 2), (9, 3), (31, 3))
        else
          if u.val < 50 then
            if u.val < 49 then
              ((27, 2), (26, 3), (9, 1))
            else
              ((9, 2), (27, 1), (31, 4))
          else
            if u.val < 51 then
              ((12, 0), (10, 0), (28, 5))
            else
              ((16, 0), (12, 5), (10, 1))
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              ((20, 0), (16, 5), (10, 2))
            else
              ((24, 0), (20, 5), (10, 3))
          else
            if u.val < 55 then
              ((28, 0), (10, 4), (24, 5))
            else
              ((31, 0), (15, 5), (11, 1))
        else
          if u.val < 58 then
            if u.val < 57 then
              ((15, 0), (11, 0), (19, 5))
            else
              ((19, 0), (11, 4), (23, 5))
          else
            if u.val < 59 then
              ((23, 0), (11, 3), (27, 5))
            else
              ((27, 0), (31, 5), (11, 2))

def c60DartLoc (u : Fin 60) (slot : Fin 3) : Nat × Nat :=
  let t := c60DartLocTriple u
  match slot.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def c60C16 : List (Fin 60) := [0, 5, 9, 51, 52, 53, 54, 50, 4, 1, 20, 23, 46, 45, 3, 2]

def c60AutA (u : Fin 60) : Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            4
          else
            if u.val < 2 then
              3
            else
              0
        else
          if u.val < 5 then
            if u.val < 4 then
              2
            else
              1
          else
            if u.val < 6 then
              50
            else
              53
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              51
            else
              52
          else
            if u.val < 10 then
              54
            else
              19
        else
          if u.val < 13 then
            if u.val < 12 then
              18
            else
              15
          else
            if u.val < 14 then
              17
            else
              16
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            40
          else
            if u.val < 17 then
              43
            else
              42
        else
          if u.val < 20 then
            if u.val < 19 then
              44
            else
              41
          else
            if u.val < 21 then
              45
            else
              48
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              49
            else
              47
          else
            if u.val < 25 then
              46
            else
              5
        else
          if u.val < 28 then
            if u.val < 27 then
              9
            else
              6
          else
            if u.val < 29 then
              7
            else
              8
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            14
          else
            if u.val < 32 then
              11
            else
              10
        else
          if u.val < 35 then
            if u.val < 34 then
              13
            else
              12
          else
            if u.val < 36 then
              36
            else
              38
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              35
            else
              39
          else
            if u.val < 40 then
              37
            else
              58
        else
          if u.val < 43 then
            if u.val < 42 then
              59
            else
              57
          else
            if u.val < 44 then
              55
            else
              56
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            25
          else
            if u.val < 47 then
              28
            else
              26
        else
          if u.val < 50 then
            if u.val < 49 then
              29
            else
              27
          else
            if u.val < 51 then
              20
            else
              24
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              21
            else
              22
          else
            if u.val < 55 then
              23
            else
              30
        else
          if u.val < 58 then
            if u.val < 57 then
              31
            else
              33
          else
            if u.val < 59 then
              34
            else
              32

def c60AutAInv (u : Fin 60) : Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            2
          else
            if u.val < 2 then
              4
            else
              3
        else
          if u.val < 5 then
            if u.val < 4 then
              1
            else
              0
          else
            if u.val < 6 then
              25
            else
              27
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              28
            else
              29
          else
            if u.val < 10 then
              26
            else
              32
        else
          if u.val < 13 then
            if u.val < 12 then
              31
            else
              34
          else
            if u.val < 14 then
              33
            else
              30
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            12
          else
            if u.val < 17 then
              14
            else
              13
        else
          if u.val < 20 then
            if u.val < 19 then
              11
            else
              10
          else
            if u.val < 21 then
              50
            else
              52
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              53
            else
              54
          else
            if u.val < 25 then
              51
            else
              45
        else
          if u.val < 28 then
            if u.val < 27 then
              47
            else
              49
          else
            if u.val < 29 then
              46
            else
              48
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            55
          else
            if u.val < 32 then
              56
            else
              59
        else
          if u.val < 35 then
            if u.val < 34 then
              57
            else
              58
          else
            if u.val < 36 then
              37
            else
              35
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              39
            else
              36
          else
            if u.val < 40 then
              38
            else
              15
        else
          if u.val < 43 then
            if u.val < 42 then
              19
            else
              17
          else
            if u.val < 44 then
              16
            else
              18
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            20
          else
            if u.val < 47 then
              24
            else
              23
        else
          if u.val < 50 then
            if u.val < 49 then
              21
            else
              22
          else
            if u.val < 51 then
              5
            else
              7
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              8
            else
              6
          else
            if u.val < 55 then
              9
            else
              43
        else
          if u.val < 58 then
            if u.val < 57 then
              44
            else
              42
          else
            if u.val < 59 then
              40
            else
              41

def c60AutB (u : Fin 60) : Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            8
          else
            if u.val < 2 then
              9
            else
              7
        else
          if u.val < 5 then
            if u.val < 4 then
              5
            else
              6
          else
            if u.val < 6 then
              30
            else
              33
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              32
            else
              34
          else
            if u.val < 10 then
              31
            else
              37
        else
          if u.val < 13 then
            if u.val < 12 then
              36
            else
              39
          else
            if u.val < 14 then
              38
            else
              35
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            17
          else
            if u.val < 17 then
              19
            else
              18
        else
          if u.val < 20 then
            if u.val < 19 then
              16
            else
              15
          else
            if u.val < 21 then
              51
            else
              53
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              54
            else
              50
          else
            if u.val < 25 then
              52
            else
              26
        else
          if u.val < 28 then
            if u.val < 27 then
              27
            else
              29
          else
            if u.val < 29 then
              25
            else
              28
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            56
          else
            if u.val < 32 then
              57
            else
              55
        else
          if u.val < 35 then
            if u.val < 34 then
              58
            else
              59
          else
            if u.val < 36 then
              42
            else
              40
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              44
            else
              41
          else
            if u.val < 40 then
              43
            else
              21
        else
          if u.val < 43 then
            if u.val < 42 then
              24
            else
              22
          else
            if u.val < 44 then
              20
            else
              23
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            0
          else
            if u.val < 47 then
              4
            else
              2
        else
          if u.val < 50 then
            if u.val < 49 then
              1
            else
              3
          else
            if u.val < 51 then
              10
            else
              12
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              13
            else
              11
          else
            if u.val < 55 then
              14
            else
              47
        else
          if u.val < 58 then
            if u.val < 57 then
              49
            else
              48
          else
            if u.val < 59 then
              46
            else
              45

def c60AutBInv (u : Fin 60) : Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            45
          else
            if u.val < 2 then
              48
            else
              47
        else
          if u.val < 5 then
            if u.val < 4 then
              49
            else
              46
          else
            if u.val < 6 then
              3
            else
              4
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              2
            else
              0
          else
            if u.val < 10 then
              1
            else
              50
        else
          if u.val < 13 then
            if u.val < 12 then
              53
            else
              51
          else
            if u.val < 14 then
              52
            else
              54
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            19
          else
            if u.val < 17 then
              18
            else
              15
        else
          if u.val < 20 then
            if u.val < 19 then
              17
            else
              16
          else
            if u.val < 21 then
              43
            else
              40
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              42
            else
              44
          else
            if u.val < 25 then
              41
            else
              28
        else
          if u.val < 28 then
            if u.val < 27 then
              25
            else
              26
          else
            if u.val < 29 then
              29
            else
              27
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            5
          else
            if u.val < 32 then
              9
            else
              7
        else
          if u.val < 35 then
            if u.val < 34 then
              6
            else
              8
          else
            if u.val < 36 then
              14
            else
              11
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              10
            else
              13
          else
            if u.val < 40 then
              12
            else
              36
        else
          if u.val < 43 then
            if u.val < 42 then
              38
            else
              35
          else
            if u.val < 44 then
              39
            else
              37
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            59
          else
            if u.val < 47 then
              58
            else
              55
        else
          if u.val < 50 then
            if u.val < 49 then
              57
            else
              56
          else
            if u.val < 51 then
              23
            else
              20
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              24
            else
              21
          else
            if u.val < 55 then
              22
            else
              32
        else
          if u.val < 58 then
            if u.val < 57 then
              30
            else
              31
          else
            if u.val < 59 then
              33
            else
              34

def c60ToZeroWord (u : Fin 60) : List Bool :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            []
          else
            if u.val < 2 then
              [false, false, false]
            else
              [false]
        else
          if u.val < 5 then
            if u.val < 4 then
              [false, false]
            else
              [false, false, false, false]
          else
            if u.val < 6 then
              [false, false, false, true]
            else
              [false, false, false, true, false, false]
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              [true, true, true, true, false]
            else
              [true, true, true, true]
          else
            if u.val < 10 then
              [false, false, false, true, false]
            else
              [false, false, false, true, true]
        else
          if u.val < 13 then
            if u.val < 12 then
              [false, false, true, false, true, false]
            else
              [true, true, true, false, true]
          else
            if u.val < 14 then
              [true, true, false, true, true]
            else
              [false, false, true, false, true]
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            [false, false, false, true, true, true]
          else
            if u.val < 17 then
              [false, true, false, true]
            else
              [false, true, false, true, false, false]
        else
          if u.val < 20 then
            if u.val < 19 then
              [false, true, false, true, false]
            else
              [false, false, true, true]
          else
            if u.val < 21 then
              [false, true]
            else
              [false, true, false, false, false]
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              [false, true, false, false]
            else
              [false, true, false]
          else
            if u.val < 25 then
              [false, true, false, false, false, false]
            else
              [false, false, false, false, true]
        else
          if u.val < 28 then
            if u.val < 27 then
              [false, false, false, false, true, false]
            else
              [true, false, true, true, true, true]
          else
            if u.val < 29 then
              [false, true, true, true, true, false]
            else
              [false, true, true, true, true]
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            [true, true, true, false, false]
          else
            if u.val < 32 then
              [true, true, true, false, false, false]
            else
              [true, true, true, false]
        else
          if u.val < 35 then
            if u.val < 34 then
              [true, false, true, true, true]
            else
              [true, true, true]
          else
            if u.val < 36 then
              [true, true, false, true, false, false]
            else
              [false, true, false, true, true]
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              [true, true, false, true, false]
            else
              [true, false, true, true]
          else
            if u.val < 40 then
              [true, true, false, true]
            else
              [false, false, true, true, true]
        else
          if u.val < 43 then
            if u.val < 42 then
              [false, true, true]
            else
              [true, false, true, false, false]
          else
            if u.val < 44 then
              [true, false, true]
            else
              [true, false, true, false]
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            [true]
          else
            if u.val < 47 then
              [true, false, false, false, false]
            else
              [true, false]
        else
          if u.val < 50 then
            if u.val < 49 then
              [true, false, false, false]
            else
              [true, false, false]
          else
            if u.val < 51 then
              [false, false, true]
            else
              [true, true, true, true, false, true]
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              [false, false, true, false, false, false]
            else
              [false, false, true, false, false]
          else
            if u.val < 55 then
              [false, false, true, false]
            else
              [true, true, false]
        else
          if u.val < 58 then
            if u.val < 57 then
              [true, true, false, false]
            else
              [true, true, false, false, false]
          else
            if u.val < 59 then
              [false, true, true, true]
            else
              [true, true]

def d20Nbrs (u : Fin 20) : Fin 20 × Fin 20 × Fin 20 :=
  if u.val < 10 then
    if u.val < 5 then
      if u.val < 2 then
        if u.val < 1 then
          (1, 4, 5)
        else
          (0, 2, 6)
      else
        if u.val < 3 then
          (1, 3, 7)
        else
          if u.val < 4 then
            (2, 4, 8)
          else
            (0, 3, 9)
    else
      if u.val < 7 then
        if u.val < 6 then
          (0, 10, 14)
        else
          (1, 10, 11)
      else
        if u.val < 8 then
          (2, 11, 12)
        else
          if u.val < 9 then
            (3, 12, 13)
          else
            (4, 13, 14)
  else
    if u.val < 15 then
      if u.val < 12 then
        if u.val < 11 then
          (5, 6, 15)
        else
          (6, 7, 16)
      else
        if u.val < 13 then
          (7, 8, 17)
        else
          if u.val < 14 then
            (8, 9, 18)
          else
            (5, 9, 19)
    else
      if u.val < 17 then
        if u.val < 16 then
          (10, 16, 19)
        else
          (11, 15, 17)
      else
        if u.val < 18 then
          (12, 16, 18)
        else
          if u.val < 19 then
            (13, 17, 19)
          else
            (14, 15, 18)

def td60Nbrs (u : Fin 60) : Fin 60 × Fin 60 × Fin 60 :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            (1, 2, 3)
          else
            if u.val < 2 then
              (0, 2, 12)
            else
              (0, 1, 15)
        else
          if u.val < 5 then
            if u.val < 4 then
              (0, 4, 5)
            else
              (3, 5, 6)
          else
            if u.val < 6 then
              (3, 4, 18)
            else
              (4, 7, 8)
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              (6, 8, 9)
            else
              (6, 7, 21)
          else
            if u.val < 10 then
              (7, 10, 11)
            else
              (9, 11, 13)
        else
          if u.val < 13 then
            if u.val < 12 then
              (9, 10, 24)
            else
              (1, 13, 14)
          else
            if u.val < 14 then
              (10, 12, 14)
            else
              (12, 13, 27)
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            (2, 16, 17)
          else
            if u.val < 17 then
              (15, 17, 30)
            else
              (15, 16, 42)
        else
          if u.val < 20 then
            if u.val < 19 then
              (5, 19, 20)
            else
              (18, 20, 31)
          else
            if u.val < 21 then
              (18, 19, 33)
            else
              (8, 22, 23)
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              (21, 23, 34)
            else
              (21, 22, 36)
          else
            if u.val < 25 then
              (11, 25, 26)
            else
              (24, 26, 37)
        else
          if u.val < 28 then
            if u.val < 27 then
              (24, 25, 39)
            else
              (14, 28, 29)
          else
            if u.val < 29 then
              (27, 29, 40)
            else
              (27, 28, 43)
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            (16, 31, 32)
          else
            if u.val < 32 then
              (19, 30, 32)
            else
              (30, 31, 45)
        else
          if u.val < 35 then
            if u.val < 34 then
              (20, 34, 35)
            else
              (22, 33, 35)
          else
            if u.val < 36 then
              (33, 34, 48)
            else
              (23, 37, 38)
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              (25, 36, 38)
            else
              (36, 37, 51)
          else
            if u.val < 40 then
              (26, 40, 41)
            else
              (28, 39, 41)
        else
          if u.val < 43 then
            if u.val < 42 then
              (39, 40, 54)
            else
              (17, 43, 44)
          else
            if u.val < 44 then
              (29, 42, 44)
            else
              (42, 43, 57)
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            (32, 46, 47)
          else
            if u.val < 47 then
              (45, 47, 49)
            else
              (45, 46, 58)
        else
          if u.val < 50 then
            if u.val < 49 then
              (35, 49, 50)
            else
              (46, 48, 50)
          else
            if u.val < 51 then
              (48, 49, 52)
            else
              (38, 52, 53)
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              (50, 51, 53)
            else
              (51, 52, 55)
          else
            if u.val < 55 then
              (41, 55, 56)
            else
              (53, 54, 56)
        else
          if u.val < 58 then
            if u.val < 57 then
              (54, 55, 59)
            else
              (44, 58, 59)
          else
            if u.val < 59 then
              (47, 57, 59)
            else
              (56, 57, 58)

def td60Faces : List (List (Fin 60)) := [
  [0, 1, 2],
  [4, 3, 5],
  [7, 6, 8],
  [10, 9, 11],
  [12, 13, 14],
  [16, 15, 17],
  [18, 19, 20],
  [21, 22, 23],
  [24, 25, 26],
  [27, 28, 29],
  [31, 30, 32],
  [34, 33, 35],
  [37, 36, 38],
  [40, 39, 41],
  [42, 43, 44],
  [46, 45, 47],
  [48, 49, 50],
  [51, 52, 53],
  [54, 55, 56],
  [57, 59, 58],
  [0, 3, 4, 6, 7, 9, 10, 13, 12, 1],
  [2, 15, 16, 30, 31, 19, 18, 5, 3, 0],
  [5, 18, 20, 33, 34, 22, 21, 8, 6, 4],
  [8, 21, 23, 36, 37, 25, 24, 11, 9, 7],
  [11, 24, 26, 39, 40, 28, 27, 14, 13, 10],
  [14, 27, 29, 43, 42, 17, 15, 2, 1, 12],
  [46, 49, 48, 35, 33, 20, 19, 31, 32, 45],
  [50, 52, 51, 38, 36, 23, 22, 34, 35, 48],
  [53, 55, 54, 41, 39, 26, 25, 37, 38, 51],
  [56, 59, 57, 44, 43, 29, 28, 40, 41, 54],
  [58, 47, 45, 32, 30, 16, 17, 42, 44, 57],
  [59, 56, 55, 53, 52, 50, 49, 46, 47, 58],
]

def td60DartLocTriple (u : Fin 60) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) :=
  if u.val < 30 then
    if u.val < 15 then
      if u.val < 7 then
        if u.val < 3 then
          if u.val < 1 then
            ((0, 0), (21, 9), (20, 0))
          else
            if u.val < 2 then
              ((20, 9), (0, 1), (25, 8))
            else
              ((0, 2), (25, 7), (21, 0))
        else
          if u.val < 5 then
            if u.val < 4 then
              ((21, 8), (20, 1), (1, 1))
            else
              ((1, 0), (22, 9), (20, 2))
          else
            if u.val < 6 then
              ((21, 7), (1, 2), (22, 0))
            else
              ((22, 8), (20, 3), (2, 1))
      else
        if u.val < 11 then
          if u.val < 9 then
            if u.val < 8 then
              ((2, 0), (23, 9), (20, 4))
            else
              ((22, 7), (2, 2), (23, 0))
          else
            if u.val < 10 then
              ((23, 8), (20, 5), (3, 1))
            else
              ((3, 0), (24, 9), (20, 6))
        else
          if u.val < 13 then
            if u.val < 12 then
              ((23, 7), (3, 2), (24, 0))
            else
              ((20, 8), (4, 0), (25, 9))
          else
            if u.val < 14 then
              ((24, 8), (20, 7), (4, 1))
            else
              ((4, 2), (24, 7), (25, 0))
    else
      if u.val < 22 then
        if u.val < 18 then
          if u.val < 16 then
            ((25, 6), (21, 1), (5, 1))
          else
            if u.val < 17 then
              ((5, 0), (30, 5), (21, 2))
            else
              ((25, 5), (5, 2), (30, 6))
        else
          if u.val < 20 then
            if u.val < 19 then
              ((21, 6), (6, 0), (22, 1))
            else
              ((21, 5), (6, 1), (26, 6))
          else
            if u.val < 21 then
              ((6, 2), (26, 5), (22, 2))
            else
              ((22, 6), (7, 0), (23, 1))
      else
        if u.val < 26 then
          if u.val < 24 then
            if u.val < 23 then
              ((22, 5), (7, 1), (27, 6))
            else
              ((7, 2), (27, 5), (23, 2))
          else
            if u.val < 25 then
              ((23, 6), (8, 0), (24, 1))
            else
              ((23, 5), (8, 1), (28, 6))
        else
          if u.val < 28 then
            if u.val < 27 then
              ((8, 2), (28, 5), (24, 2))
            else
              ((24, 6), (9, 0), (25, 1))
          else
            if u.val < 29 then
              ((24, 5), (9, 1), (29, 6))
            else
              ((9, 2), (29, 5), (25, 2))
  else
    if u.val < 45 then
      if u.val < 37 then
        if u.val < 33 then
          if u.val < 31 then
            ((30, 4), (21, 3), (10, 1))
          else
            if u.val < 32 then
              ((21, 4), (10, 0), (26, 7))
            else
              ((30, 3), (10, 2), (26, 8))
        else
          if u.val < 35 then
            if u.val < 34 then
              ((26, 4), (22, 3), (11, 1))
            else
              ((22, 4), (11, 0), (27, 7))
          else
            if u.val < 36 then
              ((26, 3), (11, 2), (27, 8))
            else
              ((27, 4), (23, 3), (12, 1))
      else
        if u.val < 41 then
          if u.val < 39 then
            if u.val < 38 then
              ((23, 4), (12, 0), (28, 7))
            else
              ((27, 3), (12, 2), (28, 8))
          else
            if u.val < 40 then
              ((28, 4), (24, 3), (13, 1))
            else
              ((24, 4), (13, 0), (29, 7))
        else
          if u.val < 43 then
            if u.val < 42 then
              ((28, 3), (13, 2), (29, 8))
            else
              ((25, 4), (14, 0), (30, 7))
          else
            if u.val < 44 then
              ((29, 4), (25, 3), (14, 1))
            else
              ((14, 2), (29, 3), (30, 8))
    else
      if u.val < 52 then
        if u.val < 48 then
          if u.val < 46 then
            ((30, 2), (26, 9), (15, 1))
          else
            if u.val < 47 then
              ((15, 0), (31, 7), (26, 0))
            else
              ((30, 1), (15, 2), (31, 8))
        else
          if u.val < 50 then
            if u.val < 49 then
              ((26, 2), (16, 0), (27, 9))
            else
              ((31, 6), (26, 1), (16, 1))
          else
            if u.val < 51 then
              ((16, 2), (31, 5), (27, 0))
            else
              ((27, 2), (17, 0), (28, 9))
      else
        if u.val < 56 then
          if u.val < 54 then
            if u.val < 53 then
              ((31, 4), (27, 1), (17, 1))
            else
              ((17, 2), (31, 3), (28, 0))
          else
            if u.val < 55 then
              ((28, 2), (18, 0), (29, 9))
            else
              ((31, 2), (28, 1), (18, 1))
        else
          if u.val < 58 then
            if u.val < 57 then
              ((18, 2), (31, 1), (29, 0))
            else
              ((29, 2), (30, 9), (19, 0))
          else
            if u.val < 59 then
              ((30, 0), (19, 2), (31, 9))
            else
              ((31, 0), (29, 1), (19, 1))

def td60DartLoc (u : Fin 60) (slot : Fin 3) : Nat × Nat :=
  let t := td60DartLocTriple u
  match slot.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def td60C16 : List (Fin 60) := [0, 3, 5, 18, 20, 33, 35, 48, 49, 46, 45, 32, 30, 16, 15, 2]

end PlanarEG.SharpData

