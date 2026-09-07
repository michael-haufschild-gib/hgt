#!/usr/bin/env python3
"""RunPod-only formatting and validation summary of the frozen experiment output."""
import json

with open('results.json') as source:
    result = json.load(source)
print('classification:', result['classification'])
print('wall seconds:', result['seconds'])
print('k X channel E diagonal sqrt_relative X_relative X_band X_omitted 4X_relative 16X_relative 64X_relative full_check')
for scale in result['scales']:
    for channel in scale['channels']:
        bands = {row['label']: row for row in channel['bands']}
        values = [channel['finite_error_energy'], channel['diagonal_covariance'],
                  bands['sqrt_X']['absolute_relative_discrepancy'],
                  bands['X']['absolute_relative_discrepancy'],
                  bands['X']['signed_band_covariance'],
                  bands['X']['signed_omitted_covariance'],
                  bands['4X']['absolute_relative_discrepancy'],
                  bands['16X']['absolute_relative_discrepancy'],
                  bands['64X']['absolute_relative_discrepancy'],
                  channel['full_covariance_absolute_discrepancy']]
        print(scale['k'], scale['X'], channel['name'],
              *[format(value, '.10g') for value in values])
channels = [channel for scale in result['scales'] for channel in scale['channels']]
print('max full covariance identity discrepancy:',
      max(channel['full_covariance_absolute_discrepancy'] for channel in channels))
print('max direct cumulative discrepancy:',
      max(check['cumulative_discrepancy'] for channel in channels
          for check in channel['direct_coordinate_checks']))
print('max omitted infinite energy upper bound, averaged source:',
      max(scale['channels'][1]['omitted_infinite_error_upper'] for scale in result['scales']))
