module L0Core
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open L0Types
open L0Crypto
open X509
open HACL

```pulse
fn create_deviceIDCRI
  (#pub_perm:perm)
  (#pub #_buf:erased (Seq.seq U8.t))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  requires 
    A.pts_to deviceID_pub #pub_perm pub **
    A.pts_to deviceIDCRI_buf _buf **
    pure (
      deviceIDCRI_len == len_of_deviceIDCRI 
                          deviceIDCSR_ingredients.version
                          deviceIDCSR_ingredients.s_common
                          deviceIDCSR_ingredients.s_org
                          deviceIDCSR_ingredients.s_country
    )
  ensures
    exists* (buf:Seq.seq U8.t).
      A.pts_to deviceID_pub #pub_perm pub **
      A.pts_to deviceIDCRI_buf buf **
      pure (
        buf `Seq.equal`
          (spec_serialize_deviceIDCRI 
            (spec_x509_get_deviceIDCRI
              deviceIDCSR_ingredients.version
              deviceIDCSR_ingredients.s_common
              deviceIDCSR_ingredients.s_org
              deviceIDCSR_ingredients.s_country
              deviceIDCSR_ingredients.ku
              pub) 
            deviceIDCRI_len)
      )
{
  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR_ingredients.version
                      deviceIDCSR_ingredients.s_common
                      deviceIDCSR_ingredients.s_org
                      deviceIDCSR_ingredients.s_country
                      deviceIDCSR_ingredients.ku
                      deviceID_pub;
  serialize_deviceIDCRI deviceIDCRI deviceIDCRI_len deviceIDCRI_buf;
}
```

// TODO: don't need full perm on all of these
```pulse
fn sign_and_finalize_deviceIDCSR
  (#priv_perm:perm)
  (#priv #_cri_buf #_csr_buf:erased (Seq.seq U8.t))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCSR_len: US.t)
  (deviceIDCSR_buf: A.larray U8.t (US.v deviceIDCSR_len))
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  requires (
    A.pts_to deviceID_priv #priv_perm priv **
    A.pts_to deviceIDCRI_buf _cri_buf **
    A.pts_to deviceIDCSR_buf _csr_buf **
    pure (
      deviceIDCRI_len == len_of_deviceIDCRI 
                          deviceIDCSR_ingredients.version
                          deviceIDCSR_ingredients.s_common
                          deviceIDCSR_ingredients.s_org
                          deviceIDCSR_ingredients.s_country /\
      0 < US.v deviceIDCRI_len /\ 
      valid_deviceIDCSR_ingredients deviceIDCRI_len /\
      deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len
    ))
  ensures (
    exists* (csr_buf:Seq.seq U8.t).
    A.pts_to deviceID_priv #priv_perm priv **
    A.pts_to deviceIDCRI_buf _cri_buf **
    A.pts_to deviceIDCSR_buf csr_buf **
    pure (
      csr_buf `Seq.equal`
        (spec_serialize_deviceIDCSR 
          deviceIDCRI_len 
          deviceIDCSR_len
          (spec_x509_get_deviceIDCSR
            deviceIDCRI_len
            _cri_buf
            (spec_ed25519_sign
              priv
              _cri_buf)))
    ))
{
  let mut deviceIDCRI_sig = [| 0uy; deviceIDCRI_len |];

  ed25519_sign deviceIDCRI_sig deviceID_priv deviceIDCRI_len deviceIDCRI_buf;

  let deviceIDCSR = x509_get_deviceIDCSR
                      deviceIDCRI_len
                      deviceIDCRI_buf
                      deviceIDCRI_sig;
                    
  serialize_deviceIDCSR deviceIDCRI_len deviceIDCSR deviceIDCSR_len deviceIDCSR_buf;
}
```

```pulse
fn create_aliasKeyTBS
  (#fwid_perm #authKey_perm #device_perm #aliasKey_perm:perm)
  (#fwid0 #authKeyID0 #deviceID_pub0 #aliasKey_pub0 #_buf:erased (Seq.seq U8.t))
  (fwid: A.larray U8.t (US.v v32us))
  (authKeyID: A.array U8.t)
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  requires 
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to authKeyID #authKey_perm authKeyID0 **
    A.pts_to deviceID_pub #device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf _buf ** 
    pure (
      aliasKeyTBS_len == len_of_aliasKeyTBS
                          aliasKeyCRT_ingredients.serialNumber
                          aliasKeyCRT_ingredients.i_common
                          aliasKeyCRT_ingredients.i_org
                          aliasKeyCRT_ingredients.i_country
                          aliasKeyCRT_ingredients.s_common
                          aliasKeyCRT_ingredients.s_org
                          aliasKeyCRT_ingredients.s_country
                          aliasKeyCRT_ingredients.l0_version
    )
  ensures exists* (buf:Seq.seq U8.t).
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to authKeyID #authKey_perm authKeyID0 **
    A.pts_to deviceID_pub #device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf buf **
    pure (
      buf `Seq.equal`
        (spec_serialize_aliasKeyTBS 
          (spec_x509_get_aliasKeyTBS
            aliasKeyCRT_ingredients
            fwid0
            deviceID_pub0
            aliasKey_pub0) 
          aliasKeyTBS_len)
    )
{
  let aliasKeyTBS = x509_get_aliasKeyTBS
                      aliasKeyCRT_ingredients
                      fwid
                      deviceID_pub
                      aliasKey_pub;

  serialize_aliasKeyTBS aliasKeyTBS aliasKeyTBS_len aliasKeyTBS_buf;
}
```

```pulse
fn sign_and_finalize_aliasKeyCRT
  (#priv_perm:perm)
  (#priv #_tbs_buf #_crt_buf:erased (Seq.seq U8.t))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT_buf: A.larray U8.t (US.v aliasKeyCRT_len))
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  requires (
    A.pts_to deviceID_priv #priv_perm priv **
    A.pts_to aliasKeyTBS_buf _tbs_buf **
    A.pts_to aliasKeyCRT_buf _crt_buf **
    pure (
      aliasKeyTBS_len == len_of_aliasKeyTBS
                          aliasKeyCRT_ingredients.serialNumber
                          aliasKeyCRT_ingredients.i_common
                          aliasKeyCRT_ingredients.i_org
                          aliasKeyCRT_ingredients.i_country
                          aliasKeyCRT_ingredients.s_common
                          aliasKeyCRT_ingredients.s_org
                          aliasKeyCRT_ingredients.s_country
                          aliasKeyCRT_ingredients.l0_version /\
      0 < US.v aliasKeyTBS_len /\ 
      valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
      aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len
    ))
  ensures (
    exists* (crt_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv #priv_perm priv **
    A.pts_to aliasKeyTBS_buf _tbs_buf **
    A.pts_to aliasKeyCRT_buf crt_buf **
    pure (
      crt_buf `Seq.equal`
        (spec_serialize_aliasKeyCRT 
          aliasKeyTBS_len 
          aliasKeyCRT_len
          (spec_x509_get_aliasKeyCRT
            aliasKeyTBS_len
            _tbs_buf
            (spec_ed25519_sign
              priv
              _tbs_buf)))
    ))
{
  let mut aliasKeyTBS_sig = [| 0uy; aliasKeyTBS_len |];

  ed25519_sign aliasKeyTBS_sig deviceID_priv aliasKeyTBS_len aliasKeyTBS_buf;

  let aliasKeyCRT = x509_get_aliasKeyCRT
                      aliasKeyTBS_len
                      aliasKeyTBS_buf
                      aliasKeyTBS_sig;
                    
  serialize_aliasKeyCRT aliasKeyTBS_len aliasKeyCRT aliasKeyCRT_len aliasKeyCRT_buf;
}
```

(* pre / post conditions for l0 *)

let aliasKey_functional_correctness alg dig_len cdi fwid aliasKey_label_len aliasKey_label 
                  aliasKey_pub aliasKey_priv 
  = (aliasKey_pub, aliasKey_priv) == derive_AliasKey_spec alg dig_len cdi fwid aliasKey_label_len aliasKey_label

let deviceIDCSR_functional_correctness alg dig_len cdi deviceID_label_len deviceID_label 
                    deviceIDCSR_ingredients deviceIDCSR_len deviceIDCSR_buf
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let deviceIDCRI_len = len_of_deviceIDCRI 
                            deviceIDCSR_ingredients.version
                            deviceIDCSR_ingredients.s_common
                            deviceIDCSR_ingredients.s_org
                            deviceIDCSR_ingredients.s_country in
      let deviceIDCRI_buf = spec_serialize_deviceIDCRI 
                              (spec_x509_get_deviceIDCRI
                                deviceIDCSR_ingredients.version
                                deviceIDCSR_ingredients.s_common
                                deviceIDCSR_ingredients.s_org
                                deviceIDCSR_ingredients.s_country
                                deviceIDCSR_ingredients.ku
                                deviceID_pub) 
                              deviceIDCRI_len in 
    deviceIDCSR_buf `Seq.equal`
      (spec_serialize_deviceIDCSR 
        deviceIDCRI_len 
        deviceIDCSR_len
        (spec_x509_get_deviceIDCSR
          deviceIDCRI_len
          deviceIDCRI_buf
          (spec_ed25519_sign
            deviceID_priv
            deviceIDCRI_buf)))

let aliasKeyCRT_functional_correctness alg dig_len cdi fwid deviceID_label_len deviceID_label
                     aliasKeyCRT_ingredients aliasKeyCRT_len aliasKeyCRT_buf aliasKey_pub
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let authKeyID = derive_AuthKeyID_spec alg deviceID_pub in
    let aliasKeyTBS_len = len_of_aliasKeyTBS
                            aliasKeyCRT_ingredients.serialNumber
                            aliasKeyCRT_ingredients.i_common
                            aliasKeyCRT_ingredients.i_org
                            aliasKeyCRT_ingredients.i_country
                            aliasKeyCRT_ingredients.s_common
                            aliasKeyCRT_ingredients.s_org
                            aliasKeyCRT_ingredients.s_country
                            aliasKeyCRT_ingredients.l0_version in
    let aliasKeyTBS_buf = (spec_serialize_aliasKeyTBS 
                            (spec_x509_get_aliasKeyTBS
                              aliasKeyCRT_ingredients
                              fwid
                              deviceID_pub
                              aliasKey_pub) 
                            aliasKeyTBS_len) in
    aliasKeyCRT_buf `Seq.equal` 
      (spec_serialize_aliasKeyCRT 
        aliasKeyTBS_len 
        aliasKeyCRT_len
        (spec_x509_get_aliasKeyCRT
          aliasKeyTBS_len
          aliasKeyTBS_buf
          (spec_ed25519_sign
            deviceID_priv
            aliasKeyTBS_buf)))

```pulse
fn l0_main'
  (cdi: A.larray U8.t (US.v dice_digest_len))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKey_priv: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len:US.t)
  (aliasKeyCRT_len:US.t)
  (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
  (deviceIDCRI_len:US.t)
  (deviceIDCSR_len:US.t)
  (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len))
  (record: l0_record_t)
  (#repr: erased l0_record_repr_t)
  (#cdi0 #deviceID_pub0 #deviceID_priv0 #aliasKey_pub0 #aliasKey_priv0 #aliasKeyCRT0 #deviceIDCSR0: erased (Seq.seq U8.t))
  (#cdi_perm #p:perm)
  requires (
    l0_record_perm record p repr **
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to deviceID_priv deviceID_priv0 **
    A.pts_to aliasKey_pub aliasKey_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 **
    A.pts_to aliasKeyCRT aliasKeyCRT0 **
    A.pts_to deviceIDCSR deviceIDCSR0 **
    pure (
      deviceIDCSR_pre record.deviceIDCSR_ingredients deviceIDCRI_len deviceIDCSR_len /\
      aliasKeyCRT_pre record.aliasKeyCRT_ingredients aliasKeyTBS_len aliasKeyCRT_len
    ))
  ensures (
      l0_record_perm record p repr **
      A.pts_to cdi #cdi_perm cdi0 **
      (exists* (deviceID_pub1 deviceID_priv1 aliasKey_pub1 aliasKey_priv1
              aliasKeyCRT1 deviceIDCSR1:Seq.seq U8.t). (
        A.pts_to deviceID_pub deviceID_pub1 **
        A.pts_to deviceID_priv deviceID_priv1 **
        A.pts_to aliasKey_pub aliasKey_pub1 **
        A.pts_to aliasKey_priv aliasKey_priv1 **
        A.pts_to aliasKeyCRT aliasKeyCRT1 **
        A.pts_to deviceIDCSR deviceIDCSR1 **
        pure (
          valid_hkdf_ikm_len dice_digest_len /\
          aliasKey_functional_correctness
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.aliasKey_label_len repr.aliasKey_label 
            aliasKey_pub1 aliasKey_priv1 /\
          deviceIDCSR_functional_correctness 
            dice_hash_alg dice_digest_len cdi0
            record.deviceID_label_len repr.deviceID_label record.deviceIDCSR_ingredients 
            deviceIDCSR_len deviceIDCSR1 /\       
          aliasKeyCRT_functional_correctness 
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.deviceID_label_len repr.deviceID_label record.aliasKeyCRT_ingredients 
            aliasKeyCRT_len aliasKeyCRT1 aliasKey_pub1
      ))))
{
  unfold (l0_record_perm record p repr);
  dice_digest_len_is_hkdf_ikm;

  derive_DeviceID dice_hash_alg 
    deviceID_pub deviceID_priv cdi 
    record.deviceID_label_len record.deviceID_label;

  derive_AliasKey dice_hash_alg
    aliasKey_pub aliasKey_priv cdi 
    record.fwid record.aliasKey_label_len record.aliasKey_label;
  
  let mut authKeyID = [| 0uy; dice_digest_len |];
  derive_AuthKeyID dice_hash_alg
    authKeyID deviceID_pub;

  let mut deviceIDCRI = [| 0uy; deviceIDCRI_len |];
  create_deviceIDCRI deviceID_pub
    deviceIDCRI_len deviceIDCRI
    record.deviceIDCSR_ingredients;
  
  sign_and_finalize_deviceIDCSR deviceID_priv 
    deviceIDCRI_len deviceIDCRI
    deviceIDCSR_len deviceIDCSR
    record.deviceIDCSR_ingredients;

  let mut aliasKeyTBS = [| 0uy; aliasKeyTBS_len |];
  create_aliasKeyTBS record.fwid authKeyID
    deviceID_pub aliasKey_pub
    aliasKeyTBS_len aliasKeyTBS
    record.aliasKeyCRT_ingredients;

  sign_and_finalize_aliasKeyCRT deviceID_priv 
    aliasKeyTBS_len aliasKeyTBS
    aliasKeyCRT_len aliasKeyCRT
    record.aliasKeyCRT_ingredients;
  
  // with s3. assert (A.pts_to deviceIDCRI s3);
  // with s4. assert (A.pts_to aliasKeyTBS s4);

  fold l0_record_perm record p repr;
}
```
let l0_main = l0_main'