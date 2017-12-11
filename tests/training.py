from learn.dsloader import *
from keras.models import Sequential
from keras.layers import Dense, Activation

train_set_X, train_set_Y = load_dataset('raw_ds.txt')
test_set_X,  test_set_Y  = load_dataset('reo_ds.txt')

print("data analyzing done.")
